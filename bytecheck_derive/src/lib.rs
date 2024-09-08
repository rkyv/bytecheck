//! Procedural macros for bytecheck.

#![deny(
    rust_2018_compatibility,
    rust_2018_idioms,
    future_incompatible,
    nonstandard_style,
    unused,
    clippy::all
)]

mod attributes;
mod repr;
mod util;

use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse_macro_input, parse_quote, spanned::Spanned, Data, DeriveInput, Error,
    Field, Fields, Ident, Index, Path,
};

use crate::{
    attributes::{Attributes, FieldAttributes},
    repr::Repr,
    util::iter_fields,
};

/// Derives `CheckBytes` for the labeled type.
///
/// This derive macro automatically adds a type bound `field: CheckBytes<__C>`
/// for each field type. This can cause an overflow while evaluating trait
/// bounds if the structure eventually references its own type, as the
/// implementation of `CheckBytes` for a struct depends on each field type
/// implementing it as well. Adding the attribute `#[check_bytes(omit_bounds)]`
/// to a field will suppress this trait bound and allow recursive structures.
/// This may be too coarse for some types, in which case additional type bounds
/// may be required with `bounds(...)`.
///
/// # Attributes
///
/// Additional arguments can be specified using attributes.
///
/// `#[bytecheck(...)]` accepts the following attributes:
///
/// ## Types only
///
/// - `bounds(...)`: Adds additional bounds to the `CheckBytes` implementation.
///   This can be especially useful when dealing with recursive structures,
///   where bounds may need to be omitted to prevent recursive type definitions.
///   In the context of the added bounds, `__C` is the name of the context
///   generic (e.g. `__C: MyContext`).
/// - `crate = ...`: Chooses an alternative crate path to import bytecheck from.
/// - `verify`: Adds an additional verification step after the validity of each
///   field has been checked. See the `Verify` trait for more information.
///
/// ## Fields only
///
/// - `omit_bounds`: Omits trait bounds for the annotated field in the generated
///   impl.
#[proc_macro_derive(CheckBytes, attributes(bytecheck))]
pub fn check_bytes_derive(
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    match derive_check_bytes(parse_macro_input!(input as DeriveInput)) {
        Ok(result) => result.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn derive_check_bytes(mut input: DeriveInput) -> Result<TokenStream, Error> {
    let attributes = Attributes::parse(&input)?;

    let crate_path = attributes.crate_path();

    let name = &input.ident;

    let mut trait_generics = input.generics.clone();

    // Split type generics for use later
    input.generics.make_where_clause();
    let (type_impl_generics, type_ty_generics, type_where_clause) =
        input.generics.split_for_impl();
    let type_where_clause = type_where_clause.unwrap();

    // Trait generics are created by modifying the type generics.

    // We add a context parameter __C for the CheckBytes type parameter.
    trait_generics.params.push(parse_quote! {
        __C: #crate_path::rancor::Fallible + ?::core::marker::Sized
    });
    // We add context error bounds to the where clause for the trait impl.
    let trait_where_clause = trait_generics.make_where_clause();
    trait_where_clause.predicates.push(match &input.data {
        // Structs and unions just propagate any errors from checking their
        // fields, so the error type of the context just needs to be `Trace`.
        Data::Struct(_) | Data::Union(_) => parse_quote! {
            <
                __C as #crate_path::rancor::Fallible
            >::Error: #crate_path::rancor::Trace
        },
        // Enums may error while checking the discriminant, so the error type of
        // the context needs to implement `Source` so we can create a new error
        // from an `InvalidEnumDiscriminantError`.
        Data::Enum(_) => parse_quote! {
            <
                __C as #crate_path::rancor::Fallible
            >::Error: #crate_path::rancor::Source
        },
    });
    // If the user specified any aditional bounds, we add them to the where
    // clause.
    if let Some(ref bounds) = attributes.bounds {
        for clause in bounds {
            trait_where_clause.predicates.push(clause.clone());
        }
    }
    // If the user specified `verify`, then we need to bound `Self: Verify<__C>`
    // so we can call `Verify::verify`.
    let verify = if attributes.verify.is_some() {
        trait_where_clause.predicates.push(parse_quote!(
            #name #type_ty_generics: #crate_path::Verify<__C>
        ));
        Some(quote! {
            <#name #type_ty_generics as #crate_path::Verify<__C>>::verify(
                unsafe { &*value },
                context,
            )?;
        })
    } else {
        None
    };

    let mut check_where = trait_where_clause.clone();
    for field in iter_fields(&input.data) {
        let field_attrs = FieldAttributes::parse(field)?;
        if field_attrs.omit_bounds.is_none() {
            let ty = &field.ty;
            check_where.predicates.push(parse_quote! {
                #ty: #crate_path::CheckBytes<__C>
            });
        }
    }

    // Split trait generics for use later
    let (trait_impl_generics, _, trait_where_clause) =
        trait_generics.split_for_impl();
    let trait_where_clause = trait_where_clause.unwrap();

    // Build CheckBytes impl
    let check_bytes_impl = match input.data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let field_checks = fields.named.iter().map(|f| {
                    let field = &f.ident;
                    let ty = &f.ty;
                    quote! {
                        <#ty as #crate_path::CheckBytes<__C>>::check_bytes(
                            ::core::ptr::addr_of!((*value).#field),
                            context
                        ).map_err(|e| {
                            <
                                <
                                    __C as #crate_path::rancor::Fallible
                                >::Error as #crate_path::rancor::Trace
                            >::trace(
                                e,
                                #crate_path::StructCheckContext {
                                    struct_name: ::core::stringify!(#name),
                                    field_name: ::core::stringify!(#field),
                                },
                            )
                        })?;
                    }
                });

                quote! {
                    #[automatically_derived]
                    // SAFETY: `check_bytes` only returns `Ok` if all of the
                    // fields of the struct are valid. If all of the fields are
                    // valid, then the overall struct is also valid.
                    unsafe impl #trait_impl_generics
                        #crate_path::CheckBytes<__C> for #name #type_ty_generics
                    #check_where
                    {
                        unsafe fn check_bytes(
                            value: *const Self,
                            context: &mut __C,
                        ) -> ::core::result::Result<
                            (),
                            <__C as #crate_path::rancor::Fallible>::Error,
                        > {
                            #(#field_checks)*
                            #verify
                            ::core::result::Result::Ok(())
                        }
                    }
                }
            }
            Fields::Unnamed(ref fields) => {
                let field_checks =
                    fields.unnamed.iter().enumerate().map(|(i, f)| {
                        let ty = &f.ty;
                        let index = Index::from(i);
                        quote! {
                            <
                                #ty as #crate_path::CheckBytes<__C>
                            >::check_bytes(
                                ::core::ptr::addr_of!((*value).#index),
                                context
                            ).map_err(|e| {
                                <
                                    <
                                        __C as #crate_path::rancor::Fallible
                                    >::Error as #crate_path::rancor::Trace
                                >::trace(
                                    e,
                                    #crate_path::TupleStructCheckContext {
                                        tuple_struct_name: ::core::stringify!(
                                            #name
                                        ),
                                        field_index: #i,
                                    },
                                )
                            })?;
                        }
                    });

                quote! {
                    #[automatically_derived]
                    // SAFETY: `check_bytes` only returns `Ok` if all of the
                    // fields of the struct are valid. If all of the fields are
                    // valid, then the overall struct is also valid.
                    unsafe impl #trait_impl_generics
                        #crate_path::CheckBytes<__C> for #name #type_ty_generics
                    #check_where
                    {
                        unsafe fn check_bytes(
                            value: *const Self,
                            context: &mut __C,
                        ) -> ::core::result::Result<
                            (),
                            <__C as #crate_path::rancor::Fallible>::Error,
                        > {
                            #(#field_checks)*
                            #verify
                            ::core::result::Result::Ok(())
                        }
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    #[automatically_derived]
                    // SAFETY: Unit structs are always valid since they have a
                    // size of 0 and no invalid bit patterns.
                    unsafe impl #trait_impl_generics
                        #crate_path::CheckBytes<__C> for #name #type_ty_generics
                    #trait_where_clause
                    {
                        unsafe fn check_bytes(
                            value: *const Self,
                            context: &mut __C,
                        ) -> ::core::result::Result<
                            (),
                            <__C as #crate_path::rancor::Fallible>::Error,
                        > {
                            #verify
                            ::core::result::Result::Ok(())
                        }
                    }
                }
            }
        },
        Data::Enum(ref data) => {
            let repr = Repr::from_attrs(&input.attrs)?;
            let primitive = match repr {
                Repr::Transparent => {
                    return Err(Error::new_spanned(
                        name,
                        "enums cannot be repr(transparent)",
                    ))
                }
                Repr::Primitive(i) => i,
                Repr::C { .. } => {
                    return Err(Error::new_spanned(
                        name,
                        "repr(C) enums are not currently supported",
                    ))
                }
                Repr::Rust { .. } => {
                    return Err(Error::new_spanned(
                        name,
                        "enums implementing CheckBytes must have an explicit \
                         repr",
                    ))
                }
            };

            let tag_variant_defs = data.variants.iter().map(|v| {
                let variant = &v.ident;
                if let Some((_, expr)) = &v.discriminant {
                    quote! { #variant = #expr }
                } else {
                    quote! { #variant }
                }
            });

            let discriminant_const_defs = data.variants.iter().map(|v| {
                let variant = &v.ident;
                quote! {
                    #[allow(non_upper_case_globals)]
                    const #variant: #primitive = Tag::#variant as #primitive;
                }
            });

            let tag_variant_values = data.variants.iter().map(|v| {
                let name = &v.ident;
                quote! { Discriminant::#name }
            });

            let variant_structs = data.variants.iter().map(|v| {
                let variant = &v.ident;
                let variant_name =
                    Ident::new(&format!("Variant{variant}"), v.span());
                match v.fields {
                    Fields::Named(ref fields) => {
                        let fields = fields.named.iter().map(|f| {
                            let name = &f.ident;
                            let ty = &f.ty;
                            quote! { #name: #ty }
                        });
                        quote! {
                            #[repr(C)]
                            struct #variant_name #type_impl_generics
                            #type_where_clause
                            {
                                __tag: Tag,
                                #(#fields,)*
                                __phantom: ::core::marker::PhantomData<
                                    #name #type_ty_generics
                                >,
                            }
                        }
                    }
                    Fields::Unnamed(ref fields) => {
                        let fields = fields.unnamed.iter().map(|f| {
                            let ty = &f.ty;
                            quote! { #ty }
                        });
                        quote! {
                            #[repr(C)]
                            struct #variant_name #type_impl_generics (
                                Tag,
                                #(#fields,)*
                                ::core::marker::PhantomData<
                                    #name #type_ty_generics
                                >
                            ) #type_where_clause;
                        }
                    }
                    Fields::Unit => quote! {},
                }
            });

            let check_arms = data.variants.iter().map(|v| {
                let variant = &v.ident;
                let variant_name =
                    Ident::new(&format!("Variant{variant}"), v.span());
                match v.fields {
                    Fields::Named(ref fields) => {
                        let checks = fields.named.iter().map(|f| {
                            check_arm_named_field(f, &crate_path, name, variant)
                        });
                        quote! { {
                            let value =
                                value.cast::<#variant_name #type_ty_generics>();
                            #(#checks)*
                        } }
                    }
                    Fields::Unnamed(ref fields) => {
                        let checks =
                            fields.unnamed.iter().enumerate().map(|(i, f)| {
                                check_arm_unnamed_field(
                                    i,
                                    f,
                                    &crate_path,
                                    name,
                                    variant,
                                )
                            });
                        quote! { {
                            let value =
                                value.cast::<#variant_name #type_ty_generics>();
                            #(#checks)*
                        } }
                    }
                    Fields::Unit => quote! { (), },
                }
            });

            let no_matching_tag_arm = quote! {
                return ::core::result::Result::Err(
                    <
                        <
                            __C as #crate_path::rancor::Fallible
                        >::Error as #crate_path::rancor::Source
                    >::new(
                        #crate_path::InvalidEnumDiscriminantError {
                            enum_name: ::core::stringify!(#name),
                            invalid_discriminant: tag,
                        }
                    )
                )
            };

            quote! {
                const _: () = {
                    #[repr(#primitive)]
                    enum Tag {
                        #(#tag_variant_defs,)*
                    }

                    struct Discriminant;

                    #[automatically_derived]
                    impl Discriminant {
                        #(#discriminant_const_defs)*
                    }

                    #(#variant_structs)*

                    #[automatically_derived]
                    // SAFETY: `check_bytes` only returns `Ok` if:
                    // - The discriminant is valid for some variant of the enum,
                    //   and
                    // - Each field of the variant struct is valid.
                    // If the discriminant is valid and the fields of the
                    // indicated variant struct are valid, then the overall enum
                    // is valid.
                    unsafe impl #trait_impl_generics
                        #crate_path::CheckBytes<__C> for #name #type_ty_generics
                    #check_where
                    {
                        unsafe fn check_bytes(
                            value: *const Self,
                            context: &mut __C,
                        ) -> ::core::result::Result<
                            (),
                            <__C as #crate_path::rancor::Fallible>::Error,
                        > {
                            let tag = *value.cast::<#primitive>();
                            match tag {
                                #(#tag_variant_values => #check_arms)*
                                _ => #no_matching_tag_arm,
                            }
                            #verify
                            ::core::result::Result::Ok(())
                        }
                    }
                };
            }
        }
        Data::Union(_) => {
            return Err(Error::new(
                input.span(),
                "CheckBytes cannot be derived for unions",
            ));
        }
    };

    Ok(check_bytes_impl)
}

fn check_arm_named_field(
    f: &Field,
    crate_path: &Path,
    name: &Ident,
    variant: &Ident,
) -> TokenStream {
    let field_name = &f.ident;
    let ty = &f.ty;
    quote! {
        <#ty as #crate_path::CheckBytes<__C>>::check_bytes(
            ::core::ptr::addr_of!((*value).#field_name),
            context
        ).map_err(|e| {
            <
                <
                    __C as #crate_path::rancor::Fallible
                >::Error as #crate_path::rancor::Trace
            >::trace(
                e,
                #crate_path::NamedEnumVariantCheckContext {
                    enum_name: ::core::stringify!(#name),
                    variant_name: ::core::stringify!(#variant),
                    field_name: ::core::stringify!(#field_name),
                },
            )
        })?;
    }
}

fn check_arm_unnamed_field(
    i: usize,
    f: &Field,
    crate_path: &Path,
    name: &Ident,
    variant: &Ident,
) -> TokenStream {
    let ty = &f.ty;
    let index = Index::from(i + 1);
    quote! {
        <#ty as #crate_path::CheckBytes<__C>>::check_bytes(
            ::core::ptr::addr_of!((*value).#index),
            context
        ).map_err(|e| {
            <
                <
                    __C as #crate_path::rancor::Fallible
                >::Error as #crate_path::rancor::Trace
            >::trace(
                e,
                #crate_path::UnnamedEnumVariantCheckContext {
                    enum_name: ::core::stringify!(#name),
                    variant_name: ::core::stringify!(#variant),
                    field_index: #index,
                },
            )
        })?;
    }
}

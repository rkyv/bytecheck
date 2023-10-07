//! Procedural macros for bytecheck.

#![deny(
    rust_2018_compatibility,
    rust_2018_idioms,
    future_incompatible,
    nonstandard_style,
    unused,
    clippy::all
)]

mod repr;

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    meta::ParseNestedMeta, parse_macro_input, parse_quote,
    punctuated::Punctuated, spanned::Spanned, AttrStyle, Data, DeriveInput,
    Error, Fields, Ident, Index, LitStr, Path, Token, WherePredicate,
};

use repr::Repr;

use crate::repr::BaseRepr;

#[derive(Default)]
struct Attributes {
    pub repr: Repr,
    pub bound: Option<Punctuated<WherePredicate, Token![,]>>,
    pub crate_path: Option<Path>,
}

fn try_set_attribute<T: ToTokens>(
    attribute: &mut Option<T>,
    value: T,
    name: &'static str,
) -> Result<(), Error> {
    if attribute.is_none() {
        *attribute = Some(value);
        Ok(())
    } else {
        Err(Error::new_spanned(
            value,
            format!("{name} already specified"),
        ))
    }
}

fn parse_check_bytes_attributes(
    attributes: &mut Attributes,
    meta: ParseNestedMeta<'_>,
) -> Result<(), Error> {
    if meta.path.is_ident("bound") {
        let lit_str = meta.value()?.parse::<LitStr>()?;
        let bound = lit_str.parse_with(Punctuated::parse_terminated)?;
        try_set_attribute(&mut attributes.bound, bound, "bound")
    } else if meta.path.is_ident("crate") {
        let crate_path = meta.value()?.parse::<LitStr>()?.parse()?;
        try_set_attribute(&mut attributes.crate_path, crate_path, "crate")
    } else {
        Err(meta.error("unrecognized check_bytes argument"))
    }
}

fn parse_attributes(input: &DeriveInput) -> Result<Attributes, Error> {
    let mut result = Attributes::default();

    for attr in input.attrs.iter() {
        if !matches!(attr.style, AttrStyle::Outer) {
            continue;
        }

        if attr.path().is_ident("check_bytes") {
            attr.parse_nested_meta(|nested| {
                parse_check_bytes_attributes(&mut result, nested)
            })?;
        } else if attr.path().is_ident("repr") {
            attr.parse_nested_meta(|nested| {
                result.repr.parse_list_meta(nested)
            })?;
        }
    }

    Ok(result)
}

/// Derives `CheckBytes` for the labeled type.
///
/// Additional arguments can be specified using the `#[check_bytes(...)]` attribute:
///
/// - `bound = "..."`: Adds additional bounds to the `CheckBytes` implementation. This can be
///   especially useful when dealing with recursive structures, where bounds may need to be omitted
///   to prevent recursive type definitions.
///
/// This derive macro automatically adds a type bound `field: CheckBytes<__C>` for each field type.
/// This can cause an overflow while evaluating trait bounds if the structure eventually references
/// its own type, as the implementation of `CheckBytes` for a struct depends on each field type
/// implementing it as well. Adding the attribute `#[omit_bounds]` to a field will suppress this
/// trait bound and allow recursive structures. This may be too coarse for some types, in which case
/// additional type bounds may be required with `bound = "..."`.
#[proc_macro_derive(CheckBytes, attributes(check_bytes, omit_bounds))]
pub fn check_bytes_derive(
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    match derive_check_bytes(parse_macro_input!(input as DeriveInput)) {
        Ok(result) => result.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn derive_check_bytes(mut input: DeriveInput) -> Result<TokenStream, Error> {
    let attributes = parse_attributes(&input)?;

    // Default to `bytecheck`, rather than `::bytecheck`,
    // to allow providing it from a reexport, e.g. `use rkyv::bytecheck;`.
    let crate_path = attributes.crate_path.unwrap_or(parse_quote!(bytecheck));

    let mut impl_input_generics = input.generics.clone();
    let impl_where_clause = impl_input_generics.make_where_clause();
    if let Some(ref bounds) = attributes.bound {
        for clause in bounds {
            impl_where_clause.predicates.push(clause.clone());
        }
    }
    impl_input_generics
        .params
        .insert(0, parse_quote! { __C: #crate_path::Context + ?Sized });

    let name = &input.ident;

    let (impl_generics, _, impl_where_clause) =
        impl_input_generics.split_for_impl();
    let impl_where_clause = impl_where_clause.unwrap();

    input.generics.make_where_clause();
    let (struct_generics, ty_generics, where_clause) =
        input.generics.split_for_impl();
    let where_clause = where_clause.unwrap();

    let check_bytes_impl = match input.data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let mut check_where = impl_where_clause.clone();
                for field in fields.named.iter().filter(|f| {
                    !f.attrs.iter().any(|a| a.path().is_ident("omit_bounds"))
                }) {
                    let ty = &field.ty;
                    check_where.predicates.push(
                        parse_quote! { #ty: #crate_path::CheckBytes<__C> },
                    );
                }

                let field_checks = fields.named.iter().map(|f| {
                    let field = &f.ident;
                    let ty = &f.ty;
                    quote_spanned! { ty.span() =>
                        <#ty as #crate_path::CheckBytes<__C>>::check_bytes(
                            ::core::ptr::addr_of!((*value).#field),
                            context
                        ).map_err(|e| <__C::Error as #crate_path::Contextual>::context(e, #crate_path::StructCheckContext {
                            struct_name: ::core::stringify!(#name),
                            field_name: ::core::stringify!(#field),
                        }))?;
                    }
                });

                quote! {
                    #[automatically_derived]
                    unsafe impl #impl_generics #crate_path::CheckBytes<__C> for #name #ty_generics #check_where {
                        unsafe fn check_bytes(
                            value: *const Self,
                            context: &mut __C,
                        ) -> ::core::result::Result<(), __C::Error> {
                            let bytes = value.cast::<u8>();
                            #(#field_checks)*
                            Ok(())
                        }
                    }
                }
            }
            Fields::Unnamed(ref fields) => {
                let mut check_where = impl_where_clause.clone();
                for field in fields.unnamed.iter().filter(|f| {
                    !f.attrs.iter().any(|a| a.path().is_ident("omit_bounds"))
                }) {
                    let ty = &field.ty;
                    check_where.predicates.push(
                        parse_quote! { #ty: #crate_path::CheckBytes<__C> },
                    );
                }

                let field_checks = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let ty = &f.ty;
                    let index = Index::from(i);
                    quote_spanned! { ty.span() =>
                        <#ty as #crate_path::CheckBytes<__C>>::check_bytes(
                            ::core::ptr::addr_of!((*value).#index),
                            context
                        ).map_err(|e| <__C::Error as #crate_path::Contextual>::context(e, #crate_path::TupleStructCheckContext {
                            tuple_struct_name: ::core::stringify!(#name),
                            field_index: #i,
                        }))?;
                    }
                });

                quote! {
                    #[automatically_derived]
                    unsafe impl #impl_generics #crate_path::CheckBytes<__C> for
                        #name #ty_generics #check_where
                    {
                        unsafe fn check_bytes(
                            value: *const Self,
                            context: &mut __C,
                        ) -> ::core::result::Result<(), __C::Error> {
                            let bytes = value.cast::<u8>();
                            #(#field_checks)*
                            Ok(())
                        }
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    #[automatically_derived]
                    unsafe impl #impl_generics #crate_path::CheckBytes<__C> for
                        #name #ty_generics #impl_where_clause
                    {
                        unsafe fn check_bytes(
                            value: *const Self,
                            context: &mut __C,
                        ) -> ::core::result::Result<(), __C::Error> {
                            Ok(())
                        }
                    }
                }
            }
        },
        Data::Enum(ref data) => {
            let repr = match attributes.repr.base_repr {
                None => return Err(Error::new_spanned(
                    name,
                    "enums implementing CheckBytes must have an explicit repr",
                )),
                Some((BaseRepr::Transparent, _)) => {
                    return Err(Error::new_spanned(
                        name,
                        "enums cannot be repr(transparent)",
                    ))
                }
                Some((BaseRepr::C, _)) => {
                    return Err(Error::new_spanned(
                        name,
                        "repr(C) enums are not currently supported",
                    ))
                }
                Some((BaseRepr::Int(i), _)) => i,
            };

            let mut check_where = impl_where_clause.clone();
            for v in data.variants.iter() {
                match v.fields {
                    Fields::Named(ref fields) => {
                        for field in fields.named.iter().filter(|f| {
                            !f.attrs
                                .iter()
                                .any(|a| a.path().is_ident("omit_bounds"))
                        }) {
                            let ty = &field.ty;
                            check_where
                                .predicates
                                .push(parse_quote! { #ty: #crate_path::CheckBytes<__C> });
                        }
                    }
                    Fields::Unnamed(ref fields) => {
                        for field in fields.unnamed.iter().filter(|f| {
                            !f.attrs
                                .iter()
                                .any(|a| a.path().is_ident("omit_bounds"))
                        }) {
                            let ty = &field.ty;
                            check_where
                                .predicates
                                .push(parse_quote! { #ty: #crate_path::CheckBytes<__C> });
                        }
                    }
                    Fields::Unit => (),
                }
            }

            let tag_variant_defs = data.variants.iter().map(|v| {
                let variant = &v.ident;
                if let Some((_, expr)) = &v.discriminant {
                    quote_spanned! { variant.span() => #variant = #expr }
                } else {
                    quote_spanned! { variant.span() => #variant }
                }
            });

            let discriminant_const_defs = data.variants.iter().map(|v| {
                let variant = &v.ident;
                quote! {
                    #[allow(non_upper_case_globals)]
                    const #variant: #repr = Tag::#variant as #repr;
                }
            });

            let tag_variant_values = data.variants.iter().map(|v| {
                let name = &v.ident;
                quote_spanned! { name.span() => Discriminant::#name }
            });

            let variant_structs = data.variants.iter().map(|v| {
                let variant = &v.ident;
                let variant_name = Ident::new(&format!("Variant{variant}"), v.span());
                match v.fields {
                    Fields::Named(ref fields) => {
                        let fields = fields.named.iter().map(|f| {
                            let name = &f.ident;
                            let ty = &f.ty;
                            quote_spanned! { f.span() => #name: #ty }
                        });
                        quote_spanned! { name.span() =>
                            #[repr(C)]
                            struct #variant_name #struct_generics #where_clause {
                                __tag: Tag,
                                #(#fields,)*
                                __phantom: ::core::marker::PhantomData<#name #ty_generics>,
                            }
                        }
                    }
                    Fields::Unnamed(ref fields) => {
                        let fields = fields.unnamed.iter().map(|f| {
                            let ty = &f.ty;
                            quote_spanned! { f.span() => #ty }
                        });
                        quote_spanned! { name.span() =>
                            #[repr(C)]
                            struct #variant_name #struct_generics (
                                Tag,
                                #(#fields,)*
                                ::core::marker::PhantomData<#name #ty_generics>
                            ) #where_clause;
                        }
                    }
                    Fields::Unit => quote! {},
                }
            });

            let check_arms = data.variants.iter().map(|v| {
                let variant = &v.ident;
                let variant_name = Ident::new(&format!("Variant{variant}"), v.span());
                match v.fields {
                    Fields::Named(ref fields) => {
                        let checks = fields.named.iter().map(|f| {
                            let field_name = &f.ident;
                            let ty = &f.ty;
                            quote! {
                                <#ty as #crate_path::CheckBytes<__C>>::check_bytes(
                                    ::core::ptr::addr_of!((*value).#field_name),
                                    context
                                ).map_err(|e| <__C::Error as #crate_path::Contextual>::context(e, #crate_path::NamedEnumVariantCheckContext {
                                    enum_name: ::core::stringify!(#name),
                                    variant_name: ::core::stringify!(#variant),
                                    field_name: ::core::stringify!(#field_name),
                                }))?;
                            }
                        });
                        quote_spanned! { variant.span() => {
                            let value = value.cast::<#variant_name #ty_generics>();
                            #(#checks)*
                        } }
                    }
                    Fields::Unnamed(ref fields) => {
                        let checks = fields.unnamed.iter().enumerate().map(|(i, f)| {
                            let ty = &f.ty;
                            let index = Index::from(i + 1);
                            quote! {
                                <#ty as #crate_path::CheckBytes<__C>>::check_bytes(
                                    ::core::ptr::addr_of!((*value).#index),
                                    context
                                ).map_err(|e| <__C::Error as #crate_path::Contextual>::context(e, #crate_path::UnnamedEnumVariantCheckContext {
                                    enum_name: ::core::stringify!(#name),
                                    variant_name: ::core::stringify!(#variant),
                                    field_index: #index,
                                }))?;
                            }
                        });
                        quote_spanned! { variant.span() => {
                            let value = value.cast::<#variant_name #ty_generics>();
                            #(#checks)*
                        } }
                    }
                    Fields::Unit => quote_spanned! { name.span() => (), },
                }
            });

            quote! {
                #[repr(#repr)]
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
                unsafe impl #impl_generics #crate_path::CheckBytes<__C> for #name #ty_generics #check_where {
                    unsafe fn check_bytes(
                        value: *const Self,
                        context: &mut __C,
                    ) -> ::core::result::Result<(), __C::Error> {
                        let tag = *value.cast::<#repr>();
                        match tag {
                            #(#tag_variant_values => #check_arms)*
                            _ => return Err(<__C::Error as #crate_path::Contextual>::new_with(|| {
                                #crate_path::InvalidEnumDiscriminantError {
                                    enum_name: ::core::stringify!(#name),
                                    invalid_discriminant: tag,
                                }
                            })),
                        }
                        Ok(())
                    }
                }
            }
        }
        Data::Union(_) => {
            return Err(Error::new(
                input.span(),
                "CheckBytes cannot be derived for unions",
            ));
        }
    };

    Ok(quote! {
        #check_bytes_impl
    })
}

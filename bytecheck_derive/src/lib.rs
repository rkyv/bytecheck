//! Procedural macros for bytecheck.

extern crate proc_macro;

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, spanned::Spanned, AttrStyle, Data, DeriveInput, Error, Fields, Ident, Index,
    Meta, NestedMeta,
};

struct Repr {
    rust: Option<Span>,
    transparent: Option<Span>,
    packed: Option<Span>,
    c: Option<Span>,
    int: Option<Ident>,
}

impl Default for Repr {
    fn default() -> Self {
        Self {
            rust: None,
            transparent: None,
            packed: None,
            c: None,
            int: None,
        }
    }
}

fn parse_attributes(input: &DeriveInput) -> Result<Repr, TokenStream> {
    let mut result = Repr::default();
    for a in input.attrs.iter() {
        if let AttrStyle::Outer = a.style {
            if let Ok(meta) = a.parse_meta() {
                if let Meta::List(meta) = meta {
                    if meta.path.is_ident("repr") {
                        for n in meta.nested.iter() {
                            if let NestedMeta::Meta(meta) = n {
                                if let Meta::Path(path) = meta {
                                    if path.is_ident("rust") {
                                        result.rust = Some(path.span());
                                    } else if path.is_ident("transparent") {
                                        result.transparent = Some(path.span());
                                    } else if path.is_ident("packed") {
                                        result.packed = Some(path.span());
                                    } else if path.is_ident("C") {
                                        result.c = Some(path.span());
                                    } else {
                                        result.int = path.get_ident().cloned();
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(result)
}

/// Derives `CheckBytes` for the labeled type.
#[proc_macro_derive(CheckBytes)]
pub fn check_bytes_derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let repr = match parse_attributes(&input) {
        Ok(repr) => repr,
        Err(errors) => return proc_macro::TokenStream::from(errors),
    };

    let check_bytes_impl = derive_check_bytes(&input, &repr);

    proc_macro::TokenStream::from(check_bytes_impl)
}

fn derive_check_bytes(input: &DeriveInput, repr: &Repr) -> TokenStream {
    let name = &input.ident;

    let generic_params = input
        .generics
        .params
        .iter()
        .map(|p| quote_spanned! { p.span() => #p });
    let generic_params = quote! { #(#generic_params,)* };

    let generic_args = input.generics.type_params().map(|p| {
        let name = &p.ident;
        quote_spanned! { name.span() => #name }
    });
    let generic_args = quote! { #(#generic_args,)* };

    let generic_predicates = match input.generics.where_clause {
        Some(ref clause) => {
            let predicates = clause.predicates.iter().map(|p| quote! { #p });
            quote! { #(#predicates,)* }
        }
        None => quote! {},
    };

    let check_bytes_impl = match input.data {
        Data::Struct(ref data) => match data.fields {
            Fields::Named(ref fields) => {
                let field_wheres = fields.named.iter().map(|f| {
                    let ty = &f.ty;
                    quote_spanned! { ty.span() => #ty: CheckBytes<__C>, }
                });

                let field_checks = fields.named.iter().map(|f| {
                        let field = &f.ident;
                        let ty = &f.ty;
                        quote_spanned! { ty.span() => <#ty as CheckBytes<__C>>::check_bytes(bytes.add(offset_of!(#name<#generic_args>, #field)), context).map_err(|e| StructCheckError { field_name: stringify!(#field), inner: e.into() })?; }
                    });

                quote! {
                    impl<__C: ?Sized, #generic_params> CheckBytes<__C> for #name<#generic_args>
                    where
                        #generic_predicates
                        #(#field_wheres)*
                    {
                        type Error = StructCheckError;

                        unsafe fn check_bytes<'a>(bytes: *const u8, context: &mut __C) -> Result<&'a Self, Self::Error> {
                            #(#field_checks)*
                            Ok(&*bytes.cast::<Self>())
                        }
                    }
                }
            }
            Fields::Unnamed(ref fields) => {
                let field_wheres = fields.unnamed.iter().map(|f| {
                    let ty = &f.ty;
                    quote_spanned! { ty.span() => #ty: CheckBytes<__C>, }
                });

                let field_checks = fields.unnamed.iter().enumerate().map(|(i, f)| {
                    let ty = &f.ty;
                    let index = Index::from(i);
                    quote_spanned! { ty.span() =>
                        <#ty as CheckBytes<__C>>::check_bytes(
                            bytes.add(offset_of!(#name<#generic_args>, #index)),
                            context
                        ).map_err(|e| TupleStructCheckError { field_index: #i, inner: e.into() })?;
                    }
                });

                quote! {
                    impl<__C: ?Sized, #generic_params> CheckBytes<__C> for #name<#generic_args>
                    where
                        #generic_predicates
                        #(#field_wheres)*
                    {
                        type Error = TupleStructCheckError;

                        unsafe fn check_bytes<'a>(bytes: *const u8, context: &mut __C) -> Result<&'a Self, Self::Error> {
                            #(#field_checks)*
                            Ok(&*bytes.cast::<Self>())
                        }
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    impl<__C: ?Sized, #generic_params> CheckBytes<__C> for #name<#generic_args>
                    where
                        #generic_predicates
                    {
                        type Error = Unreachable;

                        unsafe fn check_bytes<'a>(bytes: *const u8, context: &mut __C) -> Result<&'a Self, Self::Error> {
                            Ok(&*bytes.cast::<Self>())
                        }
                    }
                }
            }
        },
        Data::Enum(ref data) => {
            if let Some(span) = repr.rust.or(repr.transparent).or(repr.packed).or(repr.c) {
                return Error::new(span, "archive self enums must be repr(C) or repr(Int)")
                    .to_compile_error();
            }

            let repr = match repr.int {
                None => {
                    return Error::new(
                        input.span(),
                        "enums implementing CheckBytes must be repr(Int)",
                    )
                    .to_compile_error()
                }
                Some(ref repr) => repr,
            };

            let field_wheres = data.variants.iter().map(|v| match v.fields {
                Fields::Named(ref fields) => {
                    let field_wheres = fields.named.iter().map(|f| {
                        let ty = &f.ty;
                        quote_spanned! { f.span() =>  #ty: CheckBytes<__C>, }
                    });
                    quote! { #(#field_wheres)* }
                }
                Fields::Unnamed(ref fields) => {
                    let field_wheres = fields.unnamed.iter().map(|f| {
                        let ty = &f.ty;
                        quote_spanned! { f.span() =>  #ty: CheckBytes<__C>, }
                    });
                    quote! { #(#field_wheres)* }
                }
                Fields::Unit => quote! {},
            });
            let field_wheres = quote! { #(#field_wheres)* };

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
                let variant_name = Ident::new(&format!("Variant{}", variant.to_string()), v.span());
                match v.fields {
                    Fields::Named(ref fields) => {
                        let fields = fields.named.iter().map(|f| {
                            let name = &f.ident;
                            let ty = &f.ty;
                            quote_spanned! { f.span() => #name: #ty }
                        });
                        quote_spanned! { name.span() =>
                            #[repr(C)]
                            struct #variant_name<#generic_params>
                            where
                                #generic_predicates
                            {
                                __tag: Tag,
                                #(#fields,)*
                                __phantom: PhantomData<(#generic_args)>,
                            }
                        }
                    },
                    Fields::Unnamed(ref fields) => {
                        let fields = fields.unnamed.iter().map(|f| {
                            let ty = &f.ty;
                            quote_spanned! { f.span() => #ty }
                        });
                        quote_spanned! { name.span() =>
                            #[repr(C)]
                            struct #variant_name<#generic_params>(Tag, #(#fields,)* PhantomData<(#generic_args)>)
                            where
                                #generic_predicates;
                        }
                    },
                    Fields::Unit => quote! {},
                }
            });

            let check_arms = data.variants.iter().map(|v| {
                let variant = &v.ident;
                let variant_name = Ident::new(&format!("Variant{}", variant.to_string()), v.span());
                match v.fields {
                    Fields::Named(ref fields) => {
                        let checks = fields.named.iter().map(|f| {
                            let name = &f.ident;
                            let ty = &f.ty;
                            quote! {
                                <#ty as CheckBytes<__C>>::check_bytes(
                                    bytes.add(offset_of!(#variant_name<#generic_args>, #name)),
                                    context
                                ).map_err(|e| EnumCheckError::InvalidStruct {
                                    variant_name: stringify!(#variant),
                                    inner: StructCheckError {
                                        field_name: stringify!(#name),
                                        inner: e.into(),
                                    },
                                })?;
                            }
                        });
                        quote_spanned! { variant.span() => #(#checks)* }
                    }
                    Fields::Unnamed(ref fields) => {
                        let checks = fields.unnamed.iter().enumerate().map(|(i, f)| {
                            let ty = &f.ty;
                            let index = Index::from(i + 1);
                            quote! {
                                <#ty as CheckBytes<__C>>::check_bytes(
                                    bytes.add(offset_of!(#variant_name<#generic_args>, #index)),
                                    context
                                ).map_err(|e| EnumCheckError::InvalidTuple {
                                    variant_name: stringify!(#variant),
                                    inner: TupleStructCheckError {
                                        field_index: #i,
                                        inner: e.into(),
                                    },
                                })?;
                            }
                        });
                        quote_spanned! { name.span() => #(#checks)* }
                    }
                    Fields::Unit => quote_spanned! { name.span() => () },
                }
            });

            quote! {
                #[repr(#repr)]
                enum Tag {
                    #(#tag_variant_defs,)*
                }

                struct Discriminant;

                impl Discriminant {
                    #(#discriminant_const_defs)*
                }

                #(#variant_structs)*

                impl<__C: ?Sized, #generic_params> CheckBytes<__C> for #name<#generic_args>
                where
                    #generic_predicates
                    #field_wheres
                {
                    type Error = EnumCheckError<#repr>;

                    unsafe fn check_bytes<'a>(bytes: *const u8, context: &mut __C) -> Result<&'a Self, Self::Error> {
                        let tag = *bytes.cast::<#repr>();
                        match tag {
                            #(#tag_variant_values => { #check_arms },)*
                            _ => return Err(EnumCheckError::InvalidTag(tag)),
                        }
                        Ok(&*bytes.cast::<Self>())
                    }
                }
            }
        }
        Data::Union(_) => {
            return Error::new(input.span(), "CheckBytes cannot be derived for unions")
                .to_compile_error()
        }
    };

    quote! {
        const _: () = {
            use core::marker::PhantomData;
            use bytecheck::{
                CheckBytes,
                EnumCheckError,
                offset_of,
                StructCheckError,
                TupleStructCheckError,
                Unreachable,
            };

            #check_bytes_impl
        };
    }
}

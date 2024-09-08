use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{parenthesized, token, Attribute, Error, Ident, LitInt};

#[derive(Clone, Copy)]
pub enum Primitive {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
}

impl Primitive {
    const ALL: [Self; 10] = [
        Self::I8,
        Self::I16,
        Self::I32,
        Self::I64,
        Self::Isize,
        Self::U8,
        Self::U16,
        Self::U32,
        Self::U64,
        Self::Usize,
    ];

    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::Isize => "isize",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Usize => "usize",
        }
    }
}

impl ToTokens for Primitive {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ident = Ident::new(self.as_str(), Span::call_site());
        tokens.extend(quote! { #ident });
    }
}

pub enum Modifier {
    Packed(#[allow(dead_code)] usize),
    Align(#[allow(dead_code)] usize),
}

pub enum Repr {
    Transparent,
    Primitive(Primitive),
    C {
        #[allow(dead_code)]
        primitive: Option<Primitive>,
        #[allow(dead_code)]
        modifier: Option<Modifier>,
    },
    Rust {
        #[allow(dead_code)]
        modifier: Option<Modifier>,
    },
}

impl Repr {
    pub fn from_attrs(attrs: &[Attribute]) -> Result<Self, Error> {
        let mut c = false;
        let mut transparent = false;
        let mut primitive = None;
        let mut modifier = None;

        for attr in attrs.iter().filter(|a| a.meta.path().is_ident("repr")) {
            attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("C") {
                    c = true;
                    Ok(())
                } else if meta.path.is_ident("transparent") {
                    transparent = true;
                    Ok(())
                } else if let Some(&p) = Primitive::ALL
                    .iter()
                    .find(|p| meta.path.is_ident(p.as_str()))
                {
                    primitive = Some(p);
                    Ok(())
                } else if meta.path.is_ident("align") {
                    let content;
                    parenthesized!(content in meta.input);
                    let lit = content.parse::<LitInt>()?;
                    let n = lit.base10_parse()?;
                    modifier = Some(Modifier::Align(n));
                    Ok(())
                } else if meta.path.is_ident("packed") {
                    if meta.input.peek(token::Paren) {
                        let content;
                        parenthesized!(content in meta.input);
                        let lit = content.parse::<LitInt>()?;
                        let n = lit.base10_parse()?;
                        modifier = Some(Modifier::Packed(n));
                    } else {
                        modifier = Some(Modifier::Packed(1));
                    }
                    Ok(())
                } else {
                    Err(Error::new_spanned(
                        meta.path,
                        "unrecognized repr argument",
                    ))
                }
            })?;
        }

        if c {
            Ok(Repr::C {
                primitive,
                modifier,
            })
        } else if transparent {
            Ok(Repr::Transparent)
        } else if let Some(primitive) = primitive {
            Ok(Repr::Primitive(primitive))
        } else {
            Ok(Repr::Rust { modifier })
        }
    }
}

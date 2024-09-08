use quote::ToTokens;
use syn::{
    meta::ParseNestedMeta, parenthesized, parse::Parse, parse_quote,
    punctuated::Punctuated, AttrStyle, DeriveInput, Error, Field, Path, Token,
    WherePredicate,
};

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

#[derive(Default)]
pub struct Attributes {
    pub bounds: Option<Punctuated<WherePredicate, Token![,]>>,
    crate_path: Option<Path>,
    pub verify: Option<Path>,
}

impl Attributes {
    fn parse_check_bytes_attributes(
        &mut self,
        meta: ParseNestedMeta<'_>,
    ) -> Result<(), Error> {
        if meta.path.is_ident("bounds") {
            let bounds;
            parenthesized!(bounds in meta.input);
            let bounds =
                bounds.parse_terminated(WherePredicate::parse, Token![,])?;
            try_set_attribute(&mut self.bounds, bounds, "bounds")
        } else if meta.path.is_ident("crate") {
            if meta.input.parse::<Token![=]>().is_ok() {
                let path = meta.input.parse::<Path>()?;
                try_set_attribute(&mut self.crate_path, path, "crate")
            } else if meta.input.is_empty() || meta.input.peek(Token![,]) {
                try_set_attribute(
                    &mut self.crate_path,
                    parse_quote! { crate },
                    "crate",
                )
            } else {
                Err(meta.error("expected `crate` or `crate = ...`"))
            }
        } else if meta.path.is_ident("verify") {
            if !meta.input.is_empty() && !meta.input.peek(Token![,]) {
                return Err(meta.error("verify argument must be a path"));
            }

            try_set_attribute(&mut self.verify, meta.path, "verify")
        } else {
            Err(meta.error("unrecognized bytecheck argument"))
        }
    }

    pub fn parse(input: &DeriveInput) -> Result<Self, Error> {
        let mut result = Self::default();

        for attr in input.attrs.iter() {
            if !matches!(attr.style, AttrStyle::Outer) {
                continue;
            }

            if attr.path().is_ident("bytecheck") {
                attr.parse_nested_meta(|nested| {
                    result.parse_check_bytes_attributes(nested)
                })?;
            }
        }

        Ok(result)
    }

    pub fn crate_path(&self) -> Path {
        self.crate_path
            .clone()
            .unwrap_or_else(|| parse_quote! { ::bytecheck })
    }
}

#[derive(Default)]
pub struct FieldAttributes {
    pub omit_bounds: Option<Path>,
}

impl FieldAttributes {
    fn parse_meta(&mut self, meta: ParseNestedMeta<'_>) -> Result<(), Error> {
        if meta.path.is_ident("omit_bounds") {
            self.omit_bounds = Some(meta.path);
            Ok(())
        } else {
            Err(meta.error("unrecognized bytecheck arguments"))
        }
    }

    pub fn parse(input: &Field) -> Result<Self, Error> {
        let mut result = Self::default();

        for attr in input.attrs.iter() {
            if attr.path().is_ident("bytecheck") {
                attr.parse_nested_meta(|meta| result.parse_meta(meta))?;
            }
        }

        Ok(result)
    }
}

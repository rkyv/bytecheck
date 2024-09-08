use core::iter::FlatMap;

use syn::{
    punctuated::Iter, Data, DataEnum, DataStruct, DataUnion, Field, Variant,
};

type VariantFieldsFn = fn(&Variant) -> Iter<'_, Field>;

fn variant_fields(variant: &Variant) -> Iter<'_, Field> {
    variant.fields.iter()
}

pub enum FieldsIter<'a> {
    Struct(Iter<'a, Field>),
    Enum(FlatMap<Iter<'a, Variant>, Iter<'a, Field>, VariantFieldsFn>),
}

impl<'a> Iterator for FieldsIter<'a> {
    type Item = &'a Field;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Struct(iter) => iter.next(),
            Self::Enum(iter) => iter.next(),
        }
    }
}

pub fn iter_fields(data: &Data) -> FieldsIter<'_> {
    match data {
        Data::Struct(DataStruct { fields, .. }) => {
            FieldsIter::Struct(fields.iter())
        }
        Data::Enum(DataEnum { variants, .. }) => {
            FieldsIter::Enum(variants.iter().flat_map(variant_fields))
        }
        Data::Union(DataUnion { fields, .. }) => {
            FieldsIter::Struct(fields.named.iter())
        }
    }
}

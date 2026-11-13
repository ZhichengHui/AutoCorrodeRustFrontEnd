// An ADT whose field type has an associated-type projection that normalises to a type containing
// the ADT itself (as in jaq-core, where `Native<D>` reaches `Lut<Native<D>>` through
// `<D as DataT>`): its HOL type, which takes the projection's type as a parameter, would be
// infinite, so it is a placeholder type instead of a stack overflow of the frontend.

pub trait DataT {
    type V;
}

pub struct Native<D: DataT> {
    pub next: Option<Box<D::V>>,
    pub n: u32,
}

pub struct U;

impl DataT for U {
    type V = Native<U>;
}

pub fn depth(x: &Native<U>) -> u32 {
    match &x.next {
        None => x.n,
        Some(_) => x.n + 1,
    }
}

pub fn plain(a: u32) -> u32 {
    a + 1
}

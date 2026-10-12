// Generics, trait implementations, operator overloading, derived traits.

use std::ops::Add;

pub fn id<T>(x: T) -> T {
    x
}

pub fn first<A, B>(p: (A, B)) -> A {
    p.0
}

pub fn swap_pair<A, B>(p: (A, B)) -> (B, A) {
    (p.1, p.0)
}

pub struct Wrapper<T> {
    pub inner: T,
    pub tag: u8,
}

impl<T> Wrapper<T> {
    pub fn new(inner: T) -> Wrapper<T> {
        Wrapper { inner, tag: 0 }
    }

    pub fn get(self) -> T {
        self.inner
    }
}

pub fn wrap_u32(x: u32) -> u32 {
    let w = Wrapper::new(x);
    id(w.get())
}

pub fn opt_map<T>(o: Option<T>, d: T) -> T {
    match o {
        Some(v) => v,
        None => d,
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub struct V2 {
    pub a: u32,
    pub b: u32,
}

impl Add for V2 {
    type Output = V2;
    fn add(self, o: V2) -> V2 {
        V2 { a: self.a + o.a, b: self.b + o.b }
    }
}

pub trait Area {
    fn area(&self) -> u32;
}

pub struct Sq(pub u32);

impl Area for Sq {
    fn area(&self) -> u32 {
        self.0 * self.0
    }
}

pub fn use_trait(s: &Sq) -> u32 {
    s.area() + Area::area(s)
}

pub fn add_vectors(x: V2, y: V2) -> V2 {
    x + y
}

pub fn compare(x: V2, y: V2) -> bool {
    let z = x.clone();
    z == y
}

pub fn generic_pair_use() -> u32 {
    let p = swap_pair((1u32, true));
    if p.0 { first((5u32, 6u8)) } else { 0 }
}

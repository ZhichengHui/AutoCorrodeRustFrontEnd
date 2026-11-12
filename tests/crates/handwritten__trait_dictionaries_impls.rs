// Dictionaries of derived implementations (from the models of their methods), of a trait with more
// than eight methods (grouped), of an `impl Trait` type (its hidden type's implementation), the bound
// of an associated type (`IntoIterator::IntoIter: Iterator`, for a generic `for`), and a generic
// associated type with a type parameter (no dictionary field: a placeholder).
#[derive(Clone, PartialEq)]
pub struct P(pub u32);
pub fn same<T: PartialEq + Clone>(a: &T, b: &T) -> bool { a.clone() == *b }
pub fn same_p(a: &P) -> bool { same_generic(a) }
fn same_generic<T: PartialEq + Clone>(a: &T) -> bool { same(a, a) }
pub fn use_same<U: PartialEq + Clone>(u: &U, p: &P) -> bool { same(u, u) && same(p, p) }
pub trait Many {
    fn m0(&self) -> u32; fn m1(&self) -> u32; fn m2(&self) -> u32; fn m3(&self) -> u32; fn m4(&self) -> u32;
    fn m5(&self) -> u32; fn m6(&self) -> u32; fn m7(&self) -> u32; fn m8(&self) -> u32; fn m9(&self) -> u32;
}
impl Many for u32 {
    fn m0(&self) -> u32 { *self } fn m1(&self) -> u32 { *self } fn m2(&self) -> u32 { *self } fn m3(&self) -> u32 { *self }
    fn m4(&self) -> u32 { *self } fn m5(&self) -> u32 { *self } fn m6(&self) -> u32 { *self } fn m7(&self) -> u32 { *self }
    fn m8(&self) -> u32 { *self } fn m9(&self) -> u32 { *self }
}
pub fn sum_many<T: Many>(x: &T) -> u32 { x.m0() + x.m9() }
pub fn sum_many_vec<U: Many>(x: &U, y: &u32) -> u32 { sum_many(x) + sum_many(y) }
pub trait Get { fn get(&self) -> u32; }
pub struct S(pub u32);
impl Get for S { fn get(&self) -> u32 { self.0 } }
fn mk(x: u32) -> impl Get { S(x) }
pub fn twice<T: Get>(t: &T) -> u32 { t.get() + t.get() }
pub fn use_mk(x: u32) -> u32 { let g = mk(x); twice(&g) }
pub fn total<I: IntoIterator<Item = u32>>(xs: I) -> u32 { let mut s = 0; for x in xs { s += x; } s }
pub trait Family { type Of<T>; fn wrap<T>(t: T) -> Self::Of<T>; }
pub fn wrap_u32<F: Family>(x: u32) -> F::Of<u32> { F::wrap(x) }
// a projection reached through an associated type bound that is no dictionary field (it reaches the
// trait again), and one only in the type of an `Fn` bound: type variables of their own
pub trait Node { type Child: Node; fn child(&self) -> Self::Child; }
pub fn grandchild<N: Node>(n: &N) -> <N::Child as Node>::Child { n.child().child() }
pub fn apply_of<F: Family, G: Fn(F::Of<u32>) -> u32>(g: G, x: u32) -> u32 { g(F::wrap(x)) }

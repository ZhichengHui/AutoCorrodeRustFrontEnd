// Dictionary fields of methods whose names are one identifier (`lbd` and `lbd_`; an Isabelle name
// cannot end in an underscore), and a method named like the dictionary's internal names (`mk`).
pub trait Assign {
    fn lbd(&self) -> u32;
    fn lbd_(&self) -> u32;
    fn mk(&self) -> u32;
}
pub struct S(pub u32);
impl Assign for S {
    fn lbd(&self) -> u32 { self.0 }
    fn lbd_(&self) -> u32 { self.0 ^ 1 }
    fn mk(&self) -> u32 { 0 }
}
pub fn both<A: Assign>(a: &A) -> u32 { a.lbd() ^ a.lbd_() ^ a.mk() }
pub fn use_s(s: &S) -> u32 { both(s) }

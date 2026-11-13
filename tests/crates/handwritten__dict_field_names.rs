// Dictionary fields of methods whose names are one identifier (`lbd` and `lbd_`; an Isabelle name
// cannot end in an underscore), and, in a dictionary of more than 8 fields (declared in groups), a
// method named like the dictionary's constructor of the groups (`mk`).
pub trait Assign {
    fn lbd(&self) -> u32;
    fn lbd_(&self) -> u32;
    fn mk(&self) -> u32;
    fn a(&self) -> u32 { 1 }
    fn b(&self) -> u32 { 2 }
    fn c(&self) -> u32 { 3 }
    fn d(&self) -> u32 { 4 }
    fn e(&self) -> u32 { 5 }
    fn f(&self) -> u32 { 6 }
}
pub struct S(pub u32);
impl Assign for S {
    fn lbd(&self) -> u32 { self.0 }
    fn lbd_(&self) -> u32 { self.0 ^ 1 }
    fn mk(&self) -> u32 { 0 }
}
pub fn both<A: Assign>(a: &A) -> u32 { a.lbd() ^ a.lbd_() ^ a.mk() ^ a.f() }
pub fn use_s(s: &S) -> u32 { both(s) }

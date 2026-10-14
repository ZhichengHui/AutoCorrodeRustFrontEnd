pub trait Tr { type Out; }
pub struct Foo;
impl Tr for Foo { type Out = &'static mut u32; }
pub struct Holder { pub r: <Foo as Tr>::Out }
pub fn bump(h: Holder) { *h.r += 1; }

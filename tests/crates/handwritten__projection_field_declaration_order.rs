pub trait Tr { type Out; }
pub struct Foo;
impl Tr for Foo { type Out = Bar; }
pub struct Baz { pub x: <Foo as Tr>::Out }
pub struct Bar(pub u32);
pub fn get(b: &Baz) -> u32 { b.x.0 }

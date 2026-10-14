pub trait Tr { type Out; }
pub struct Foo;
impl Tr for Foo { type Out = Option<Box<Node>>; }
pub struct Node { pub v: u32, pub next: <Foo as Tr>::Out }
pub fn val(n: &Node) -> u32 { n.v }

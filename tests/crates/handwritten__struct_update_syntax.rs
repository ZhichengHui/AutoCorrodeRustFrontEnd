#[derive(Clone, Copy)] pub struct P { pub x: u32, pub y: u32 } pub fn f(p: P) -> P { P { x: 7, ..p } }

#[derive(Clone, Copy, PartialEq)] pub struct P { pub x: u32 } pub fn f(a: P, b: P) -> bool { a.clone() == b }

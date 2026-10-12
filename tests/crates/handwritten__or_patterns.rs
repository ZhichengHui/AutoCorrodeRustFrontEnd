#[derive(Clone, Copy)] pub enum C { R, G, B } pub fn f(c: C) -> u8 { match c { C::R | C::G => 1, C::B => 2 } }

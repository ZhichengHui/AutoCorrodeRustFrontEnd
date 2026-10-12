pub enum S { C(u32), R { w: u32, h: u32 }, E }
pub fn f(s: &S) -> u32 { match s { S::C(r) => 3 * r, S::R { w, h } => w * h, S::E => 0 } }

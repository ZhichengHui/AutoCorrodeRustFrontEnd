pub enum S { C(u32), E } pub fn f(s: S) -> u32 { match s { S::C(r) if r > 10 => 1, S::C(0) => 2, S::C(r) => r, S::E => 4 } }

pub trait S { fn a(&self) -> u32; } pub fn f(s: &dyn S) -> u32 { s.a() }

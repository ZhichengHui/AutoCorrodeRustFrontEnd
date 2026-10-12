pub trait S { fn a(&self) -> u32; } pub fn f<T: S>(s: &T) -> u32 { s.a() + 1 }

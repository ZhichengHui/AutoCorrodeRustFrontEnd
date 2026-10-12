pub trait A { fn area(&self) -> u32; } pub struct S(pub u32); impl A for S { fn area(&self) -> u32 { self.0 * self.0 } } pub fn f(s: &S) -> u32 { s.area() }

pub struct A { pub x: u32 } pub struct B { pub a: A, pub w: u32 }
pub fn f() -> u32 { let mut b = B { a: A { x: 1 }, w: 2 }; b.a.x += 5; b.w = 4; b.a.x + b.w }

pub mod m { pub fn g(x: u32) -> u32 { x + 1 } } pub fn f(a: u32) -> u32 { fn h(v: u32) -> u32 { v * 2 } const K: u32 = 4; m::g(h(a)) + K }

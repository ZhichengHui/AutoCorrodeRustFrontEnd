pub struct P { pub x: u32, pub y: u32 } pub fn f(p: P) -> u32 { let P { x, y } = p; x * y }

pub struct P { pub x: u32 }
impl P { pub fn bump(&mut self, d: u32) { self.x += d; } pub fn get(&self) -> u32 { self.x } }
pub fn f() -> u32 { let mut p = P { x: 1 }; p.bump(2); p.get() }

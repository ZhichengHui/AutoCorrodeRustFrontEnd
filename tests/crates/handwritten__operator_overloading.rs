use std::ops::Add; #[derive(Clone, Copy)] pub struct V { pub a: u32 }
impl Add for V { type Output = V; fn add(self, o: V) -> V { V { a: self.a + o.a } } }
pub fn f(x: V, y: V) -> V { x + y }

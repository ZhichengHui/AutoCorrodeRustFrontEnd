pub struct H<'a> { pub r: &'a mut u32 } pub fn f(h: H) { *h.r = 1; }

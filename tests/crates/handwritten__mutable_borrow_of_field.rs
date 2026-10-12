pub struct C { pub hits: u32 } pub fn inc(c: &mut u32) { *c += 1; } pub fn f(c: &mut C) { inc(&mut c.hits); }

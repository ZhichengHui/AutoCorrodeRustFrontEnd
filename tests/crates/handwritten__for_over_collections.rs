pub fn f(v: &Vec<u32>, w: &[u32]) -> u32 { let a = [1u32, 2]; let mut s = 0; for x in v.iter() { s += x; } for x in w { s += x; } for x in a.iter() { s += *x; } s }

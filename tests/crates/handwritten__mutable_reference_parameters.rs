pub fn swap(a: &mut u32, b: &mut u32) { let t = *a; *a = *b; *b = t; } pub fn f() -> u32 { let mut x = 1; let mut y = 2; swap(&mut x, &mut y); x }

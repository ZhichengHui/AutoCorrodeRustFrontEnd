pub fn f(a: Option<u32>) -> u32 { let Some(v) = a else { return 0; }; v + 1 }

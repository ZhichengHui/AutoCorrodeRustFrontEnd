pub fn f(n: u32) -> u32 { let mut i = 0; let r = loop { i += 1; if i > n { break i; } }; r }

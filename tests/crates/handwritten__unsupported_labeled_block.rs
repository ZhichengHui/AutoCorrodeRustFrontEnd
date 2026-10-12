pub fn f(c: bool) -> u32 { 'b: { if c { break 'b 1; } 2 } }

pub fn f(x: u8, y: u8) -> u8 { ((x & y) ^ (x | y)) << 1 >> 2 }

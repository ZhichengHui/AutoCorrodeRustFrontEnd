pub fn fact(n: u64) -> u64 { if n == 0 { 1 } else { n * fact(n - 1) } }

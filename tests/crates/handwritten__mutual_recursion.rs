pub fn even(n: u32) -> bool { if n == 0 { true } else { odd(n - 1) } } pub fn odd(n: u32) -> bool { if n == 0 { false } else { even(n - 1) } }

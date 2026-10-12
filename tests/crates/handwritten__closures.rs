pub fn f(x: u32, k: u32) -> u32 { let g = |v: u32| v * k; let h = || 5u32; g(x) + h() }

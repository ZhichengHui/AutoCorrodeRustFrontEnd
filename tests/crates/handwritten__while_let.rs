pub fn f(s: Option<u32>) -> u32 { let mut c = s; let mut n = 0; while let Some(v) = c { n += 1; c = if v == 0 { None } else { Some(v - 1) }; } n }

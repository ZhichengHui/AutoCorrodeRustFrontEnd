pub fn f(a: Option<u32>) -> u32 { match a { Some(n @ 1..=9) => n, Some(n) => n + 100, None => 0 } }

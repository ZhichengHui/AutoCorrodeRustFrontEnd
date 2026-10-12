pub fn f(a: Option<u32>, b: bool) -> u32 { if let Some(x) = a && b { x } else { 0 } }

pub fn f(a: Option<u32>, b: Option<u32>) -> u32 { match (a, b) { (Some(x), Some(y)) => x + y, (Some(x), None) => x, (None, _) => 0 } }

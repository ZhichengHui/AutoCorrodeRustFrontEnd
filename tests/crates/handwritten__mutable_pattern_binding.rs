pub fn f(a: Option<u32>) -> u32 { match a { Some(mut v) => { v += 1; v } None => 0 } }

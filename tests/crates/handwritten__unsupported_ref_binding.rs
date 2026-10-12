pub fn f(o: &Option<u32>) -> u32 { match *o { Some(ref v) => *v, None => 0 } }

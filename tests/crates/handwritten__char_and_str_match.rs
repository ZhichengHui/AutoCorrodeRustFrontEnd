pub fn f(c: char, s: &str) -> u32 { (match c { 'a' => 1, _ => 2 }) + (match s { "one" => 1, _ => 0 }) }

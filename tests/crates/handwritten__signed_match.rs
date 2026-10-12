pub fn f(x: i32) -> i32 { match x { 0 => 0, -1 => -1, i32::MIN..=-2 => -2, _ => 1 } }

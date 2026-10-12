pub fn f(v: &[u32]) -> u32 { match v { [a, ..] => *a, [] => 0 } }

pub enum L { N, C(u32, Box<L>) } pub fn sum(l: &L) -> u32 { match l { L::N => 0, L::C(v, r) => v + sum(r) } }

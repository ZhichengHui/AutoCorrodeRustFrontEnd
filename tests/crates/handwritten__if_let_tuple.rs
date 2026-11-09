pub fn sum_two(v: &mut Vec<u32>) -> u32 {
    if let (Some(b), Some(a)) = (v.pop(), v.pop()) { a + b } else { 0 }
}

pub fn first_is_zero(p: (u8, u8)) -> bool {
    if let (0, _) = p { true } else { false }
}

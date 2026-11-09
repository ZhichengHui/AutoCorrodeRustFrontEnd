pub fn sum_two(v: &mut Vec<u32>) -> u32 {
    if let (Some(b), Some(a)) = (v.pop(), v.pop()) { a + b } else { 0 }
}

pub fn first_is_zero(p: (u8, u8)) -> bool {
    if let (0, _) = p { true } else { false }
}

pub fn nested(x: Option<(Option<u32>, Option<u32>)>) -> u32 {
    if let Some((Some(a), Some(b))) = x { a + b } else { 0 }
}

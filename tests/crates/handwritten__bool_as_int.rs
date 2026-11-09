pub fn lit_code(var: u32, negated: bool) -> u32 {
    (var << 1) | (negated as u32)
}

pub fn sign(neg: bool) -> i8 {
    1 - 2 * (neg as i8)
}

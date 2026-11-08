#![feature(int_roundings)]
pub fn neg(x: i32, y: i8) -> (i32, i8, i8) { (-x, -y, -128_i8) }
pub fn bits(x: i64, s: i32) -> (i64, i64, i64, i64) { (!x, x << s, x >> 3_u8, x & -1 | 2 ^ x) }
pub fn mixed(a: i16, b: u32, c: isize) -> (i64, u64, isize) { (-(a as i64) * 2, !(b as i16) as u64, c as i32 as isize) }
pub fn compound(mut x: i32, y: i32) -> i32 { x += y; x -= 1; x *= 2; x /= y; x %= 7; x <<= 1_i64; x >>= y; x }
pub fn methods(a: i32, b: i32, c: u32) -> (Option<i32>, Option<i32>, i32, i32, i32, std::cmp::Ordering) {
    (a.checked_add(b), a.checked_mul(b), a.saturating_sub(b), a.wrapping_add_unsigned(c), a.div_ceil(b), a.cmp(&b))
}
pub fn range(x: i64) -> u8 { match x { i64::MIN..=-100 => 0, -99..0 => 1, 0 => 2, _ => 3 } }

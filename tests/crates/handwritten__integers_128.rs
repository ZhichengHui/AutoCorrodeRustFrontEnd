// 128-bit integers: literals, arithmetic, comparison and casts.
pub fn add(a: u128, b: u128) -> u128 { a + b + 340282366920938463463374607431768211455u128 * 0 }
pub fn neg(a: i128) -> i128 { a - (-170141183460469231731687303715884105728i128) + 1 }
pub fn widen(a: u64) -> u128 { (a as u128) << 64 | a as u128 }
pub fn narrow(a: i128) -> i64 { (a >> 64) as i64 }
pub fn max(a: u128, b: u128) -> u128 { if a > b { a } else { b } }

// Signed integers (AutoCorrode signed-integers extension).

pub fn neg(x: i32) -> i32 {
    -x
}

pub fn abs(x: i64) -> i64 {
    if x < 0 { -x } else { x }
}

pub fn literals() -> i32 {
    let a: i32 = -5;
    let b = 7i32;
    let c = -2147483648i32;
    let d: i8 = -128;
    a + b + (c / 2) / 1000 + (d as i32)
}

pub fn div_rem(a: i32, b: i32) -> (i32, i32) {
    (a / b, a % b)
}

pub fn shifts(a: i16) -> i16 {
    (a >> 2) << 1
}

pub fn casts(a: i8, b: u8, c: isize) -> i64 {
    let x = a as i64;
    let y = b as i16;
    let z = c as i32;
    let w = a as u32;
    x + y as i64 + z as i64 + w as i64
}

pub fn sign(x: i32) -> i32 {
    match x {
        0 => 0,
        -1 => -1,
        i32::MIN..=-2 => -2,
        _ => 1,
    }
}

pub fn signed_loop(n: i32) -> i32 {
    let mut s = 0;
    for i in -3..n {
        s += i;
    }
    s
}

pub fn mixed(mut acc: i64, k: i64) -> i64 {
    acc -= k;
    acc *= -1;
    acc %= 7;
    acc
}

pub fn min_max() -> i64 {
    i64::MAX - 1 + i64::MIN / 2
}

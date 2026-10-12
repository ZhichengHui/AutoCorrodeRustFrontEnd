// Basic arithmetic, let bindings, if/else, calls, mutable locals.

pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

pub fn max3(a: u64, b: u64, c: u64) -> u64 {
    let m = if a > b { a } else { b };
    if m > c { m } else { c }
}

pub fn sum_to(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0u32;
    while i < n {
        i += 1;
        s = s + i;
    }
    s
}

pub fn twice_add(x: u32) -> u32 {
    let y = add(x, x);
    add(y, 1)
}

pub fn bits(x: u8, y: u8) -> u8 {
    let a = x & y;
    let b = x | y;
    let c = a ^ b;
    (c << 1) >> 2
}

pub fn cmp_chain(x: u16) -> bool {
    x >= 3 && x <= 10 || x == 42 || !(x != 7)
}

pub fn early_return(x: u32) -> u32 {
    if x == 0 {
        return 1;
    }
    let y = x * 2;
    y % 7
}

pub fn unit_fn(x: u32) {
    let _ = add(x, 1);
}

pub fn casts(x: u8, y: u64) -> u32 {
    let a = x as u32;
    let b = y as u32;
    a + b + (x as u16) as u32
}

pub fn mut_param(mut x: u32) -> u32 {
    x += 5;
    x *= 2;
    x -= 1;
    x
}

pub fn div_assign(mut x: u64) -> u64 {
    x /= 3;
    x
}

pub fn shadow(x: u32) -> u32 {
    let x = x + 1;
    let x = x * 2;
    x
}

pub fn deferred_init(c: bool) -> u32 {
    let x;
    if c {
        x = 1;
    } else {
        x = 2;
    }
    x
}

pub const LIMIT: u32 = 100;

pub fn uses_const(x: u32) -> bool {
    x < LIMIT && x < u32::MAX
}

pub fn chars_and_strings(c: char) -> bool {
    let s: &str = "hello";
    let _t = s;
    c == 'a' || c == '\n'
}

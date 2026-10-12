// Standard library: functions with uRust models and external templates.

pub fn opt_ops(a: Option<u32>) -> u32 {
    let b = a.ok_or(7u8);
    let c = a.expect("value");
    let d = if a.is_none() { 0 } else { 1 };
    c + d + if b.is_ok() { 1 } else { 0 }
}

pub fn res_ops(r: Result<u32, u8>) -> Option<u32> {
    let x = r.unwrap_or(3);
    let _y = r.expect("res");
    if r.is_err() { None } else { r.ok().map(|v| v + x) }
}

pub fn vec_ops(n: u32) -> usize {
    let mut v: Vec<u32> = Vec::new();
    let w = vec![1u32, 2, 3];
    for i in 0..n {
        v.push(i);
    }
    v.len() + w.len()
}

pub fn checked(a: u32, b: u32) -> Option<u32> {
    a.checked_add(b)
}

pub fn ordering(a: u64, b: u64) -> u8 {
    match a.cmp(&b) {
        std::cmp::Ordering::Less => 0,
        std::cmp::Ordering::Equal => 1,
        std::cmp::Ordering::Greater => 2,
    }
}

pub fn strings(s: &str) -> String {
    let t = String::from(s);
    t
}

pub fn min_max(a: u32, b: u32) -> u32 {
    std::cmp::min(a, b) + std::cmp::max(a, b)
}

pub fn swap_mem(a: &mut u32, b: &mut u32) {
    std::mem::swap(a, b);
}

pub fn assertions(x: u32) -> u32 {
    assert!(x > 0);
    assert_eq!(x, x);
    debug_assert!(x < 100, "too big");
    if x == 50 {
        panic!("fifty");
    }
    if x == 51 {
        unreachable!();
    }
    x
}

pub fn printing(x: u32) -> u32 {
    println!("x = {}", x);
    x
}

pub fn boxed(x: u32) -> u32 {
    let b = Box::new(x);
    *b + 1
}

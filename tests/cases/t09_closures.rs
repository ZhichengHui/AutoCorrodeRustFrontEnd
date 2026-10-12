// Closures that do not mutate captured variables.

pub fn apply(x: u32) -> u32 {
    let add_one = |v: u32| v + 1;
    add_one(add_one(x))
}

pub fn capture(x: u32, k: u32) -> u32 {
    let scale = |v: u32| v * k;
    scale(x) + scale(1)
}

pub fn no_args() -> u32 {
    let five = || 5u32;
    five() + 1
}

pub fn two_args(a: u64, b: u64) -> u64 {
    let f = |x: u64, y: u64| {
        let s = x + y;
        s * 2
    };
    f(a, b)
}

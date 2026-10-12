// Loops: for over ranges and collections, while, loop, break/continue, labels.

pub fn sum_range(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..n {
        s += i;
    }
    s
}

pub fn sum_inclusive(n: u64) -> u64 {
    let mut s = 0;
    for i in 1..=n {
        s += i;
    }
    s
}

pub fn sum_vec(v: &Vec<u32>) -> u32 {
    let mut s = 0;
    for x in v.iter() {
        s += x;
    }
    s
}

pub fn sum_slice(v: &[u8]) -> u8 {
    let mut s = 0;
    for x in v {
        s += x;
    }
    s
}

pub fn first_even(v: &[u32]) -> Option<u32> {
    for x in v.iter() {
        if x % 2 == 0 {
            return Some(*x);
        }
    }
    None
}

pub fn skip_odds(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..n {
        if i % 2 == 1 {
            continue;
        }
        if i > 50 {
            break;
        }
        s += i;
    }
    s
}

pub fn find_loop(n: u32) -> u32 {
    let mut i = 0;
    loop {
        if i * i >= n {
            break;
        }
        i += 1;
    }
    i
}

pub fn nested_labels(n: u32) -> u32 {
    let mut count = 0;
    'outer: for i in 0..n {
        for j in 0..n {
            if j > i {
                continue 'outer;
            }
            if i + j > 10 {
                break 'outer;
            }
            count += 1;
        }
    }
    count
}

pub fn labeled_while(n: u32) -> u32 {
    let mut i = 0;
    let mut hits = 0;
    'w: while i < n {
        i += 1;
        let mut j = 0;
        while j < i {
            j += 1;
            if j == 3 {
                continue 'w;
            }
            hits += 1;
        }
    }
    hits
}

pub fn return_in_loop(n: u32) -> u32 {
    let mut i = 0;
    while i < n {
        if i == 7 {
            return 70;
        }
        i += 1;
    }
    i
}

pub fn array_literal() -> u32 {
    let a = [1u32, 2, 3, 4];
    let mut s = 0;
    for x in a.iter() {
        s += *x;
    }
    s + a[2] + a.len() as u32
}

pub fn tuple_pattern_loop(v: &[(u32, u32)]) -> u32 {
    let mut s = 0;
    for (a, b) in v.iter() {
        s += a * b;
    }
    s
}

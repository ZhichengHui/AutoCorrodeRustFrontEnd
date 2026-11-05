pub fn sum_until_zero(xs: &[u32]) -> u32 {
    let mut s = 0;
    for x in xs {
        if *x == 0 {
            break;
        }
        s += *x;
    }
    s
}

pub fn sum_skipping(xs: Vec<u32>, skip: u32) -> u32 {
    let mut s = 0;
    for x in xs {
        if x == skip {
            continue;
        }
        s += x;
    }
    s
}

pub fn count_below(n: u32, limit: u32) -> u32 {
    let mut c = 0;
    for i in 0..n {
        if i >= limit {
            break;
        }
        if i % 3 == 0 {
            continue;
        }
        c += 1;
    }
    c
}

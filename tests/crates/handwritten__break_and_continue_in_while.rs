pub fn sum_odd_until(n: u32, stop: u32) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while i < n {
        i += 1;
        if i % 2 == 0 {
            continue;
        }
        if i > stop {
            break;
        }
        s += i;
    }
    s
}

pub fn first_square_at_least(n: u32) -> u32 {
    let mut i = 0;
    while i < n {
        if i * i >= n {
            return i;
        }
        i += 1;
    }
    n
}

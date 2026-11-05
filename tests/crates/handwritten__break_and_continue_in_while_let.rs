pub fn pop_until(mut v: Vec<u32>, stop: u32) -> u32 {
    let mut s = 0;
    while let Some(x) = v.pop() {
        if x == stop {
            break;
        }
        if x % 2 == 0 {
            continue;
        }
        s += x;
    }
    s
}

pub enum Item {
    Num(u32),
    End,
}

pub fn sum_items(items: &[Item]) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while let Item::Num(x) = &items[i] {
        i += 1;
        if *x == 0 {
            continue;
        }
        if i >= items.len() {
            break;
        }
        s += *x;
    }
    s
}

pub fn sum_while_small(v: &[u32]) -> u32 {
    let mut i = 0;
    let mut s = 0;
    while let Some(1..=9) = v.get(i).copied() {
        s += v[i];
        i += 1;
        if s > 100 {
            break;
        }
    }
    s
}

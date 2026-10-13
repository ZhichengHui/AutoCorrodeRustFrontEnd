pub fn read_mutable_local() -> u32 {
    let mut pairs = [(3u32, 0u32), (5, 1)];
    pairs[1].1
}

pub fn read_through_reference(v: &mut Vec<(usize, usize)>, j: usize) -> bool {
    v[j].0 > v[0].0
}

pub fn write_and_borrow() -> u32 {
    let mut pairs = [(3u32, 0u32), (5, 1)];
    pairs[1].1 = 7;
    pairs[1].1 += 1;
    let r = &mut pairs[0].0;
    *r += 2;
    pairs[1].1 + pairs[0].0
}

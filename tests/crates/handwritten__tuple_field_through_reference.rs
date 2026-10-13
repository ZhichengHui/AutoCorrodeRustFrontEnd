pub fn read_mutable_local() -> u32 {
    let mut t = (1u8, 2u32, 3u64);
    t.1
}

pub fn read_array_element() -> u64 {
    let mut ts = [(1u8, 2u32, 3u64), (4, 5, 6)];
    ts[1].2
}

pub fn write_and_borrow() -> u64 {
    let mut ts = [(1u8, 2u32, 3u64), (4, 5, 6)];
    ts[1].0 = 7;
    ts[1].1 += 1;
    let r = &mut ts[0].2;
    *r += 2;
    ts[1].0 as u64 + ts[1].1 as u64 + ts[0].2
}

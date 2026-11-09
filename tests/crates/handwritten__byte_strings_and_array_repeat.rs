pub fn magic() -> &'static [u8] {
    b"GET "
}

pub fn empty() -> &'static [u8] {
    b""
}

pub fn zeros() -> [u32; 4] {
    [0u32; 4]
}

pub fn count_get(xs: &[u8]) -> usize {
    let table = [false; 256];
    let mut n = 0;
    for x in xs {
        if !table[*x as usize] && xs.len() >= magic().len() {
            n += 1;
        }
    }
    n
}

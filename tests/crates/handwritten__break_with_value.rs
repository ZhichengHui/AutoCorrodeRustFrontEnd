pub fn first_multiple(n: u32, k: u32) -> u32 {
    let mut i = 1;
    loop {
        if (i * k) % n == 0 {
            break i * k;
        }
        i += 1;
    }
}

pub fn count_a(s: &str) -> u32 {
    let mut n = 0;
    for c in s.chars() {
        if c == 'a' {
            n += 1;
        }
    }
    n
}

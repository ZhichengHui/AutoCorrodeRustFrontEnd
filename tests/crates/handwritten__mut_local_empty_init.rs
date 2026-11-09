pub fn counts(xs: &[u32]) -> usize {
    let mut seen = Vec::new();
    seen.resize(xs.len(), 0u32);
    seen.len()
}

pub fn last_even(xs: &[u32]) -> bool {
    let mut found = None;
    for x in xs {
        if x % 2 == 0 {
            found = Some(*x);
        }
    }
    found.is_some()
}

pub fn with_capacity(n: usize) -> usize {
    let mut v = Vec::with_capacity(n);
    v.push(1u8);
    v.len()
}

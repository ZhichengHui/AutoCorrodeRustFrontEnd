pub fn sum_some(xs: &[Option<u32>]) -> u32 {
    let mut s = 0;
    for o in xs {
        let x = match o {
            Some(0) => continue,
            Some(x) => *x,
            None => break,
        };
        s += x;
    }
    s
}

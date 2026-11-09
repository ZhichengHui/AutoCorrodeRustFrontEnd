pub fn tail_sum(v: &[u32], a: usize) -> u32 {
    let mut s = 0;
    for x in &v[a..] {
        s += *x;
    }
    s
}

pub fn head(v: &Vec<u8>, b: usize) -> Vec<u8> {
    v[..b].to_vec()
}

pub fn head_incl(v: &[u8], b: usize) -> usize {
    v[..=b].len()
}

pub fn all(v: &[u8]) -> usize {
    v[..].len()
}

pub fn zero_tail(v: &mut Vec<u8>, a: usize) {
    for x in v[a..].iter_mut() {
        *x = 0;
    }
}

pub fn zero_tail_for(v: &mut [u8], a: usize) {
    for x in &mut v[a..] {
        *x = 0;
    }
}

pub fn tail_via_variable(v: &[u8], a: usize) -> usize {
    let r = a..;
    v[r].len()
}

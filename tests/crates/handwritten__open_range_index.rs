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

pub fn first_of_tail(v: &mut Vec<u8>) {
    let x = &mut v[1..][0];
    *x = 5;
}

pub struct Buf(pub Vec<u8>);

impl std::ops::Index<std::ops::Range<usize>> for Buf {
    type Output = [u8];
    fn index(&self, r: std::ops::Range<usize>) -> &[u8] {
        &self.0[r]
    }
}

impl std::ops::IndexMut<std::ops::Range<usize>> for Buf {
    fn index_mut(&mut self, r: std::ops::Range<usize>) -> &mut [u8] {
        &mut self.0[r]
    }
}

pub fn local_range_borrow(b: &mut Buf) -> usize {
    let s = &mut b[1..3];
    s.len()
}

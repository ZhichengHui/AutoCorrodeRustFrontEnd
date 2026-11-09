pub struct Pair {
    pub a: u32,
    pub b: Option<u32>,
}

pub fn first(p: &Pair) -> u32 {
    let Pair { ref a, .. } = *p;
    *a
}

pub fn second_or(p: &Pair, d: u32) -> u32 {
    match p.b {
        Some(ref x) => *x,
        None => d,
    }
}

pub fn len_of(v: &Vec<u8>) -> usize {
    let ref w = *v;
    w.len()
}

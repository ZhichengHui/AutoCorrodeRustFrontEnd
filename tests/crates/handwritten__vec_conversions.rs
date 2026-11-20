pub fn convert(xs: &[u8], n: usize) -> bool {
    let a = vec![1u8, 2, 3];
    let b = vec![0u8; n];
    let c = xs.to_vec();
    let d: Vec<u8> = Vec::from([4u8, 5]);
    let e: Vec<u8> = a.iter().copied().collect();
    let f = c.clone();
    let s: &[u8] = d.as_slice();
    let g: Box<[u8]> = b.into_boxed_slice();
    let h: Vec<u8> = Default::default();
    a == e && f != h && s.len() + g.len() > 0
}

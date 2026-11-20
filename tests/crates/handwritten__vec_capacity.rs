pub fn grow(n: usize) -> usize {
    let mut v: Vec<u32> = Vec::with_capacity(n);
    v.reserve(4);
    v.push(1);
    v.reserve_exact(2);
    v.shrink_to(1);
    v.shrink_to_fit();
    v.capacity() + v.len()
}

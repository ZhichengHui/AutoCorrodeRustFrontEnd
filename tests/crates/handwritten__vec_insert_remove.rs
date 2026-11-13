pub fn edit(v: &mut Vec<i64>, x: i64) -> i64 {
    v.insert(0, x);
    let a = v.remove(0);
    v.push(a);
    let b = v.swap_remove(0);
    v.extend_from_slice(&[b, b]);
    v.resize(3, 7);
    v.truncate(2);
    let c = v.pop().unwrap_or(0);
    if v.is_empty() { v.clear(); }
    a + b + c
}

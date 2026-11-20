fn bump(s: &mut [u32]) {
    for x in s.iter_mut() {
        *x += 1;
    }
}

pub fn walk(mut v: Vec<u32>) -> u32 {
    bump(&mut v);
    v.sort();
    for x in &mut v {
        *x *= 2;
    }
    v[0] = 3;
    let mut s = v[1..].len() as u32;
    for x in &v {
        s += x;
    }
    for x in v {
        s += x;
    }
    s
}

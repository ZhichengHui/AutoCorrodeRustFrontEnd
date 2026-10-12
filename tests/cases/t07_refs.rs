// References: &mut parameters, swaps, borrows of locals and fields, Vec indexing.

pub struct Counter {
    pub hits: u32,
    pub misses: u32,
}

pub fn swap(a: &mut u32, b: &mut u32) {
    let t = *a;
    *a = *b;
    *b = t;
}

pub fn incr(c: &mut u32) {
    *c += 1;
}

pub fn use_swap() -> u32 {
    let mut x = 1;
    let mut y = 2;
    swap(&mut x, &mut y);
    incr(&mut x);
    x * 10 + y
}

pub fn record(c: &mut Counter, hit: bool) {
    if hit {
        incr(&mut c.hits);
    } else {
        c.misses += 1;
    }
}

pub fn total(c: &Counter) -> u32 {
    c.hits + c.misses
}

pub fn run(n: u32) -> u32 {
    let mut c = Counter { hits: 0, misses: 0 };
    for i in 0..n {
        record(&mut c, i % 3 == 0);
    }
    total(&c)
}

pub fn read_index(v: &Vec<u64>, i: usize) -> u64 {
    v[i] + v[0]
}

pub fn write_index(v: &mut Vec<u64>, i: usize) {
    v[i] = 5;
    v[0] += v[i];
}

pub fn slice_len(v: &[u8]) -> usize {
    v.len()
}

pub fn reborrow(a: &mut u32) {
    let r = &mut *a;
    *r = 3;
    incr(r);
}

pub fn shared_ref(x: &u32) -> u32 {
    *x + 1
}

pub fn pass_shared() -> u32 {
    let mut v = 4;
    v += 1;
    shared_ref(&v)
}

pub fn ref_to_ref(a: &mut &mut u32) {
    **a = 9;
}

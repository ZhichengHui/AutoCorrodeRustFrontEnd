// Small algorithms in the style of real library code.

pub fn binary_search(xs: &[u32], target: u32) -> Option<usize> {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] == target {
            return Some(mid);
        } else if xs[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

pub fn bubble_sort(v: &mut Vec<u32>) {
    let n = v.len();
    let mut i = 0;
    while i < n {
        let mut j = 0;
        while j + 1 < n - i {
            if v[j] > v[j + 1] {
                let t = v[j];
                v[j] = v[j + 1];
                v[j + 1] = t;
            }
            j += 1;
        }
        i += 1;
    }
}

pub fn count_matches(xs: &[u8], b: u8) -> usize {
    let mut c = 0;
    for x in xs {
        if *x == b {
            c += 1;
        }
    }
    c
}

pub fn max_of(xs: &[i32]) -> Option<i32> {
    if xs.len() == 0 {
        return None;
    }
    let mut m = xs[0];
    for i in 1..xs.len() {
        if xs[i] > m {
            m = xs[i];
        }
    }
    Some(m)
}

pub struct Stack {
    pub items: Vec<u64>,
    pub limit: usize,
}

#[derive(PartialEq, Clone, Copy)]
pub enum StackError {
    Full,
    Empty,
}

impl Stack {
    pub fn new(limit: usize) -> Stack {
        Stack { items: Vec::new(), limit }
    }

    pub fn push(&mut self, x: u64) -> Result<(), StackError> {
        if self.items.len() >= self.limit {
            return Err(StackError::Full);
        }
        self.items.push(x);
        Ok(())
    }

    pub fn pop(&mut self) -> Result<u64, StackError> {
        match self.items.pop() {
            Some(x) => Ok(x),
            None => Err(StackError::Empty),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.items.len() == 0
    }
}

pub fn stack_demo() -> Result<u64, StackError> {
    let mut s = Stack::new(2);
    s.push(1)?;
    s.push(2)?;
    let a = s.pop()?;
    let b = s.pop()?;
    Ok(a + b)
}

pub fn checksum(data: &[u8]) -> u16 {
    let mut a: u16 = 1;
    let mut b: u16 = 0;
    for d in data {
        a = (a + *d as u16) % 251;
        b = (b + a) % 251;
    }
    (b << 8) | a
}

pub fn collatz_steps(mut n: u64) -> u32 {
    let mut steps = 0;
    while n != 1 {
        n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
        steps += 1;
    }
    steps
}

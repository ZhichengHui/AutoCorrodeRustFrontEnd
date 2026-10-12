// Combinations of features.

pub const ORIGIN: Point = Point { x: 0, y: 0 };
pub const LIMIT: u8 = 200;
pub static NAMES: [u8; 3] = [1, 2, 3];

#[derive(Clone, Copy)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

pub struct Grid {
    pub cells: Vec<u8>,
    pub width: usize,
}

impl Grid {
    pub fn get(&self, x: usize, y: usize) -> u8 {
        self.cells[y * self.width + x]
    }

    pub fn set(&mut self, x: usize, y: usize, v: u8) {
        let i = y * self.width + x;
        self.cells[i] = v;
    }

    pub fn bump_all(&mut self) {
        let n = self.cells.len();
        for i in 0..n {
            if self.cells[i] < LIMIT {
                self.cells[i] += 1;
            }
        }
    }

    pub fn drain_sum(&mut self) -> u64 {
        let mut s: u64 = 0;
        while let Some(v) = self.cells.pop() {
            s += v as u64;
        }
        s
    }
}

pub fn manhattan(a: Point, b: Point) -> i32 {
    let dx = if a.x > b.x { a.x - b.x } else { b.x - a.x };
    let dy = if a.y > b.y { a.y - b.y } else { b.y - a.y };
    dx + dy
}

pub fn from_origin(p: Point) -> i32 {
    manhattan(ORIGIN, p)
}

pub fn classify(v: u8) -> u8 {
    match v {
        LIMIT => 1,
        0 => 2,
        _ => 3,
    }
}

pub fn shadow_in_arms(o: Option<u32>) -> u32 {
    let x = 10;
    match o {
        Some(x) => x,
        None => x,
    }
}

pub fn first_name() -> u8 {
    NAMES[0]
}

pub fn is_digit(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4'
        || c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}

pub fn nested_early(v: &[u32]) -> u32 {
    let mut i = 0;
    while i < v.len() {
        let mut j = i;
        while j < v.len() {
            if v[i] + v[j] == 10 {
                return (i * 100 + j) as u32;
            }
            j += 1;
        }
        i += 1;
    }
    0
}

pub fn apply_twice<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(f(x))
}

pub fn use_apply() -> u32 {
    apply_twice(|v| v * 3, 2)
}

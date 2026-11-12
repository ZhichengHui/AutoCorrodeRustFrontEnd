// Constants translated from their evaluated values (`urust_const_data`), and constants whose
// values have no data form (translated from their initialisers).

#[derive(Clone, Copy)]
pub struct Bits(pub u64);

#[derive(Clone, Copy)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

#[derive(Clone, Copy)]
pub enum Shape {
    Dot,
    Circle(u8),
    Rect { w: u16, h: u16 },
}

#[derive(Clone, Copy)]
pub enum Color {
    Red,
    Green,
    Blue,
}

const fn bits_table() -> [Bits; 8] {
    let mut t = [Bits(0); 8];
    let mut i = 0;
    while i < 8 {
        t[i] = Bits(1u64 << (i * 8));
        i += 1;
    }
    t
}

pub const TABLE: [Bits; 8] = bits_table();
pub const GRID: [[u8; 3]; 2] = [[1, 2, 3], [4, 5, 6]];
pub const PAIR: (u32, bool, i8) = (7, true, -3);
pub const POINTS: [Point; 2] = [Point { x: -1, y: 2 }, Point { x: 3, y: -4 }];
pub const SHAPES: [Shape; 3] = [Shape::Dot, Shape::Circle(5), Shape::Rect { w: 2, h: 3 }];
pub const COLORS: [Color; 3] = [Color::Blue, Color::Red, Color::Green];
pub const NEG: [i64; 3] = [i64::MIN, -1, i64::MAX];
pub const FLAGS: [bool; 2] = [false, true];
pub const MAYBE: [Option<u8>; 2] = [None, Some(9)];
pub const UNIT: () = ();
pub const EMPTY: [u32; 0] = [];

// no data form: a float, a string
pub const RATIO: (u8, f64) = (1, 0.5);
pub const NAME: &str = "table";

pub struct Holder;

impl Holder {
    pub const LIMITS: [u16; 2] = [10, 20];
}

pub fn lookup(i: usize) -> u64 {
    TABLE[i].0 + GRID[1][2] as u64 + PAIR.0 as u64 + POINTS[0].y as u64 + Holder::LIMITS[1] as u64
}

pub fn shape_size(i: usize) -> u16 {
    match SHAPES[i] {
        Shape::Dot => 0,
        Shape::Circle(r) => r as u16,
        Shape::Rect { w, h } => w * h,
    }
}

pub fn is_blue(i: usize) -> bool {
    matches!(COLORS[i], Color::Blue) && FLAGS[1] && NEG[1] < 0 && EMPTY.len() == 0
}

pub fn first_ratio() -> u8 {
    RATIO.0 + NAME.len() as u8 + match MAYBE[1] { Some(v) => v, None => 0 }
}

pub fn unit() {
    UNIT
}

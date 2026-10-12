// Structs: definition, construction, field access and update, methods.

#[derive(Clone, Copy, PartialEq)]
pub struct Point {
    pub x: u32,
    pub y: u32,
}

pub struct Rect {
    pub origin: Point,
    pub w: u32,
    pub h: u32,
}

pub struct Meters(pub u64);

pub struct Pair(pub u8, pub bool);

pub struct Marker;

impl Point {
    pub fn new(x: u32, y: u32) -> Point {
        Point { x, y }
    }

    pub fn origin() -> Point {
        Point { y: 0, x: 0 }
    }

    pub fn sum(&self) -> u32 {
        self.x + self.y
    }

    pub fn shift(&mut self, dx: u32) {
        self.x += dx;
        self.y = self.y + dx;
    }

    pub fn swapped(self) -> Point {
        Point { x: self.y, y: self.x }
    }

    pub fn x_mut(&mut self) -> &mut u32 {
        &mut self.x
    }
}

impl Rect {
    pub fn area(&self) -> u32 {
        self.w * self.h
    }

    pub fn move_right(&mut self, d: u32) {
        self.origin.x += d;
    }

    pub fn corner(&self) -> Point {
        Point::new(self.origin.x + self.w, self.origin.y + self.h)
    }
}

pub fn make_rect(w: u32, h: u32) -> Rect {
    Rect { origin: Point::origin(), w, h }
}

pub fn update_syntax(p: Point) -> Point {
    Point { x: 7, ..p }
}

pub fn use_methods(a: u32) -> u32 {
    let mut p = Point::new(a, 2);
    p.shift(3);
    let q = p.swapped();
    let r = make_rect(2, 3);
    q.sum() + r.area() + r.corner().x
}

pub fn through_ref(p: &mut Point) {
    *p.x_mut() = 10;
    p.y = 20;
}

pub fn local_struct_update() -> u32 {
    let mut r = make_rect(1, 1);
    r.move_right(5);
    r.w = 4;
    r.origin.y = 9;
    r.origin.x + r.w + r.origin.y
}

pub fn tuple_struct(m: Meters, p: Pair) -> u64 {
    let Meters(v) = m;
    let c = if p.1 { p.0 as u64 } else { 0 };
    v + c
}

pub fn wrap(v: u64) -> Meters {
    Meters(v)
}

pub fn unit_struct() -> Marker {
    Marker
}

pub fn destructure(p: Point) -> u32 {
    let Point { x, y } = p;
    x * y
}

pub fn eq_points(a: Point, b: Point) -> bool {
    a == b && a.clone() != Point::origin()
}

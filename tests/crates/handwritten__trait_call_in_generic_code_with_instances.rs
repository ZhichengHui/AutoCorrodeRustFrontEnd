pub trait Shape {
    fn area(&self) -> u32;
    fn double(&self) -> u32 {
        self.area() * 2
    }
}

pub struct Square(pub u32);

pub struct Rect {
    pub w: u32,
    pub h: u32,
}

impl Shape for Square {
    fn area(&self) -> u32 {
        self.0 * self.0
    }
}

impl Shape for Rect {
    fn area(&self) -> u32 {
        self.w * self.h
    }
    fn double(&self) -> u32 {
        self.area() + self.area()
    }
}

pub fn total<T: Shape>(s: &T) -> u32 {
    s.area() + s.double()
}

pub fn use_both() -> u32 {
    total(&Square(3)) + total(&Rect { w: 2, h: 5 })
}

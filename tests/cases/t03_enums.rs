// Enums, patterns, Option/Result, `?`, if-let, while-let, let-else.

pub enum Shape {
    Circle(u32),
    Rect { w: u32, h: u32 },
    Empty,
}

#[derive(Clone, Copy, PartialEq)]
pub enum Color {
    Red,
    Green,
    Blue,
}

pub fn area(s: &Shape) -> u32 {
    match s {
        Shape::Circle(r) => 3 * r * r,
        Shape::Rect { w, h } => w * h,
        Shape::Empty => 0,
    }
}

pub fn make(kind: u8) -> Shape {
    if kind == 0 {
        Shape::Empty
    } else if kind == 1 {
        Shape::Circle(2)
    } else {
        Shape::Rect { w: 2, h: 3 }
    }
}

pub fn with_guard(s: Shape) -> u32 {
    match s {
        Shape::Circle(r) if r > 10 => 1,
        Shape::Circle(0) => 2,
        Shape::Rect { w: 1, .. } => 3,
        Shape::Rect { h, .. } => h,
        _ => 4,
    }
}

pub fn color_code(c: Color) -> u8 {
    match c {
        Color::Red | Color::Green => 1,
        Color::Blue => 2,
    }
}

pub fn is_red(c: Color) -> bool {
    matches!(c, Color::Red)
}

pub fn opt_add(a: Option<u32>, b: u32) -> u32 {
    match a {
        Some(x) => x + b,
        None => b,
    }
}

pub fn opt_chain(a: Option<u32>) -> Option<u32> {
    let x = a?;
    Some(x + 1)
}

pub fn res_chain(a: Result<u32, u8>) -> Result<u32, u8> {
    let x = a?;
    if x > 100 {
        return Err(1);
    }
    Ok(x * 2)
}

pub fn if_let(a: Option<u64>) -> u64 {
    if let Some(v) = a {
        v
    } else {
        0
    }
}

pub fn if_let_lit(a: Option<u64>) -> bool {
    if let Some(5) = a { true } else { false }
}

pub fn let_else(a: Option<u32>) -> u32 {
    let Some(v) = a else {
        return 0;
    };
    v + 1
}

pub fn nested(a: Option<Option<u32>>) -> u32 {
    match a {
        Some(Some(v)) => v,
        Some(None) => 1,
        None => 2,
    }
}

pub fn tuple_match(a: Option<u32>, b: Option<u32>) -> u32 {
    match (a, b) {
        (Some(x), Some(y)) => x + y,
        (Some(x), None) => x,
        (None, Some(y)) => y,
        (None, None) => 0,
    }
}

pub fn binding_at(a: Option<u32>) -> u32 {
    match a {
        Some(n @ 1..=9) => n,
        Some(n) => n + 100,
        None => 0,
    }
}

pub fn mut_binding(a: Option<u32>) -> u32 {
    match a {
        Some(mut v) => {
            v += 1;
            v
        }
        None => 0,
    }
}

pub fn count_down(start: Option<u32>) -> u32 {
    let mut cur = start;
    let mut steps = 0;
    while let Some(v) = cur {
        steps += 1;
        cur = if v == 0 { None } else { Some(v - 1) };
    }
    steps
}

pub fn unwraps(a: Option<u32>, b: Result<u32, u32>) -> u32 {
    a.unwrap() + b.unwrap() + if a.is_some() { 1 } else { 0 }
}

// `match` on integers, chars, bools and strings.

pub fn classify(x: u8) -> u8 {
    match x {
        0 => 10,
        1 | 2 | 3 => 20,
        4..=9 => 30,
        n if n > 200 => n - 200,
        _ => 40,
    }
}

pub fn exact(x: u32) -> u32 {
    match x {
        1 => 100,
        2 => 200,
        _ => 0,
    }
}

pub fn letters(c: char) -> u32 {
    match c {
        'a' => 1,
        'b' | 'c' => 2,
        _ => 3,
    }
}

pub fn flags(b: bool, c: bool) -> u8 {
    match (b, c) {
        (true, true) => 3,
        (true, false) => 2,
        (false, _) => 0,
    }
}

pub fn named(s: &str) -> u32 {
    match s {
        "one" => 1,
        "two" => 2,
        _ => 0,
    }
}

pub fn bound(x: u64) -> u64 {
    match x {
        small @ 0..=9 => small,
        big => big / 10,
    }
}

pub fn tuple_of_ints(p: (u8, u8)) -> u8 {
    match p {
        (0, y) => y,
        (x, 0) => x,
        (x, y) => x + y,
    }
}

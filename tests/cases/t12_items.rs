// Items: modules (flattened), nested functions, consts, statics, name clashes, ordering.

pub const BASE: u32 = 10;
pub static SCALE: u32 = 3;

pub mod geometry {
    pub struct P {
        pub x: u32,
    }

    impl P {
        pub fn new(x: u32) -> P {
            P { x }
        }
    }

    pub mod inner {
        pub fn helper(x: u32) -> u32 {
            x + super::super::BASE
        }
    }
}

pub struct Q {
    pub y: u32,
}

impl Q {
    pub fn new(y: u32) -> Q {
        Q { y }
    }
}

pub fn outer(a: u32) -> u32 {
    fn local_helper(v: u32) -> u32 {
        v * 2
    }
    const LOCAL: u32 = 4;
    local_helper(a) + LOCAL
}

pub fn uses_modules(a: u32) -> u32 {
    let p = geometry::P::new(a);
    let q = Q::new(a);
    geometry::inner::helper(p.x) + q.y + SCALE * BASE
}

// defined before its callee: the translation must reorder
pub fn caller() -> u32 {
    callee() + 1
}

pub fn callee() -> u32 {
    2
}

// names that clash with HOL / uRust keywords and constants
pub fn keywords(len: u32, map: u32, of: u32, case: u32, id: u32) -> u32 {
    len + map + of + case + id
}

pub fn underscore_params(_unused: u32, _: u32, x: u32) -> u32 {
    x
}

pub fn tuple_params((a, b): (u32, u32)) -> u32 {
    a + b
}

pub fn many_args(a: u8, b: u8, c: u8, d: u8, e: u8, f: u8, g: u8, h: u8, i: u8) -> u8 {
    a + b + c + d + e + f + g + h + i
}

pub fn call_many() -> u8 {
    many_args(1, 2, 3, 4, 5, 6, 7, 8, 9)
}

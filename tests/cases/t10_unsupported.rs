// Features that uRust does not support: each must become a placeholder,
// and the generated program must still be accepted by Isabelle.

use std::cell::Cell;
use std::collections::HashMap;

pub fn float(x: f64) -> f64 {
    x * 2.5
}

pub fn wide(x: u128) -> u128 {
    x + 1
}

pub trait Shape {
    fn area(&self) -> u32;
    fn twice(&self) -> u32 {
        2 * self.area()
    }
}

pub struct Sq(pub u32);

impl Shape for Sq {
    fn area(&self) -> u32 {
        self.0 * self.0
    }
}

pub fn dynamic(s: &dyn Shape) -> u32 {
    s.area()
}

pub fn generic_trait<T: Shape>(s: &T) -> u32 {
    s.area()
}

pub fn default_method(s: &Sq) -> u32 {
    s.twice()
}

pub async fn later() -> u32 {
    1
}

pub union U {
    pub a: u32,
    pub b: f32,
}

pub static mut COUNTER: u32 = 0;

pub fn raw(p: *const u32) -> u32 {
    unsafe { *p }
}

pub fn break_value(n: u32) -> u32 {
    let mut i = 0;
    let r = loop {
        i += 1;
        if i > n {
            break i * 2;
        }
    };
    r
}

pub fn labeled_block(c: bool) -> u32 {
    let v = 'blk: {
        if c {
            break 'blk 1;
        }
        2
    };
    v
}

pub fn repeat() -> [u8; 4] {
    [0u8; 4]
}

pub fn mut_closure() -> u32 {
    let mut n = 0;
    let mut inc = || n += 1;
    inc();
    inc();
    n
}

pub fn ref_binding(o: &Option<u32>) -> u32 {
    match *o {
        Some(ref v) => *v,
        None => 0,
    }
}

pub fn slice_rest(v: &[u32]) -> u32 {
    match v {
        [first, ..] => *first,
        [] => 0,
    }
}

pub struct Buf<const N: usize> {
    pub data: [u8; N],
}

pub fn const_gen<const N: usize>(b: Buf<N>) -> usize {
    N + b.data.len()
}

unsafe extern "C" {
    pub fn c_abs(x: i32) -> i32;
}

pub fn call_c(x: i32) -> i32 {
    unsafe { c_abs(x) }
}

pub fn impl_trait() -> impl Fn(u32) -> u32 {
    |x| x + 1
}

pub fn hashmap(m: &HashMap<u32, u32>) -> u32 {
    *m.get(&1).unwrap_or(&0)
}

pub fn format_it(x: u32) -> String {
    format!("{}", x)
}

pub enum Discr {
    A = 1,
    B = 5,
}

pub fn discr(d: Discr) -> u32 {
    d as u32
}

pub struct Guard(pub u32);

impl Drop for Guard {
    fn drop(&mut self) {
        self.0 = 0;
    }
}

pub fn cell(c: &Cell<u32>) {
    c.set(c.get() + 1);
}

pub fn bytes() -> &'static [u8] {
    b"abc"
}

pub fn bool_cast(b: bool) -> u32 {
    b as u32
}

pub fn non_ascii() -> &'static str {
    "héllo"
}

pub fn inline_const() -> u32 {
    const { 1 + 2 }
}

pub fn let_chain(a: Option<u32>, b: bool) -> u32 {
    if let Some(x) = a && b { x } else { 0 }
}

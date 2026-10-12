use std::cell::Cell; pub fn f(c: &Cell<u32>) { c.set(c.get() + 1); }

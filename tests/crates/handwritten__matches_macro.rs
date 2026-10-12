pub enum C { R, G } pub fn f(c: C) -> bool { matches!(c, C::R) }

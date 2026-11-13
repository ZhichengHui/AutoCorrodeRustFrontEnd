pub fn singleton<T>(x: T) -> Vec<T> {
    let mut v = Vec::new();
    v.push(x);
    v
}

#[derive(Clone, PartialEq, Default)]
pub struct Bag {
    pub items: Vec<u16>,
}

pub fn same(a: &Bag, b: &Bag) -> bool {
    a == b
}

pub fn copy(a: &Bag) -> Bag {
    a.clone()
}

pub fn fresh() -> Bag {
    Bag::default()
}

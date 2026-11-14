#[derive(PartialEq)]
pub struct Bag {
    pub items: Vec<u16>,
    pub tag: u8,
}

#[derive(PartialEq)]
pub struct Pair {
    pub left: Bag,
    pub right: Bag,
}

#[derive(PartialEq)]
pub enum Slot {
    Empty,
    Full(Vec<u8>),
}

pub fn differ(a: &Bag, b: &Bag) -> bool {
    a != b
}

pub fn same_pair(a: &Pair, b: &Pair) -> bool {
    a == b
}

pub fn same_slot(a: &Slot, b: &Slot) -> bool {
    a == b
}

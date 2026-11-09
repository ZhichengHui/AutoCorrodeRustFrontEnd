pub struct Marker();

pub enum E {
    A(),
    B(u8),
}

pub fn make() -> Marker {
    Marker()
}

pub fn pick(x: u8) -> E {
    if x == 0 { E::A() } else { E::B(x) }
}

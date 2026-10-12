pub enum E { L(u32), N(Box<T>) } pub enum T { A(u32), W(Box<E>) }
pub fn ev(e: &E) -> u32 { match e { E::L(v) => *v, E::N(t) => et(t) } }
pub fn et(t: &T) -> u32 { match t { T::A(v) => *v, T::W(e) => ev(e) } }

// Type variables that would occur only in a function body (not in its signature): each would become
// an extra `itself` parameter of the constant, so that its callers no longer type-check.

pub trait Marker { fn tag() -> u8; }
pub struct A;
impl Marker for A { fn tag() -> u8 { 1 } }

// `M` occurs only in the body (a turbofish)
pub fn marked<M: Marker>(x: u8) -> u8 { let v: Vec<M> = Vec::new(); x + v.len() as u8 }
pub fn call_marked(x: u8) -> u8 { marked::<A>(x) }

// a type parameter of the result only, fixed by the caller
pub struct On;
pub trait Static<T> { fn val(self) -> T; }
impl<T> Static<Option<T>> for On { fn val(self) -> Option<T> { None } }
pub fn padded(p: On, n: usize) -> usize { match Static::<Option<u8>>::val(p) { None => n, Some(_) => n + 1 } }
pub fn call_padded(n: usize) -> usize { padded(On, n) }

// the allocator of a `Vec` argument does not determine the `Drain` result
pub fn drop_front(v: &mut Vec<u32>, k: usize) -> usize { let _ = v.drain(0..k); v.len() }
pub fn call_drop_front(v: &mut Vec<u32>) -> usize { drop_front(v, 1) }

// a call of a function returning `!` coerced to another type
pub fn fail() -> ! { panic!("fail") }
pub fn checked(a: u32, b: u32) -> u32 { match a.checked_sub(b) { Some(r) => r, None => fail() } }
pub fn call_checked(a: u32) -> u32 { checked(a, 1) }

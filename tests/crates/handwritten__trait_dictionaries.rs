// Generic code calling methods of trait bounds: dictionary passing. Local traits with a default
// method, a supertrait with an associated type, an implementation with a bound, generic callers of
// generic functions, standard-library bounds (`Clone`, `PartialOrd` through `>`), a method with a
// type parameter of its own (not a dictionary field), and a recursive generic function.
pub trait Shape {
    fn area(&self) -> u32;
    fn double(&self) -> u32 { self.area() * 2 }
}
pub trait Named: Shape {
    type Id;
    fn id(&self) -> Self::Id;
}
pub struct Sq(pub u32);
impl Shape for Sq {
    fn area(&self) -> u32 { self.0 * self.0 }
}
impl Named for Sq {
    type Id = u32;
    fn id(&self) -> u32 { self.0 }
}
pub struct Pair<T>(pub T, pub T);
impl<T: Shape> Shape for Pair<T> {
    fn area(&self) -> u32 { self.0.area() + self.1.area() }
}
pub fn total<T: Shape>(x: &T, y: &T) -> u32 { x.area() + y.double() }
pub fn name_id<T: Named>(x: &T) -> T::Id { let _a = x.area(); x.id() }
pub fn twice_total<U: Shape>(x: &U) -> u32 { total(x, x) + total(x, x) }
pub fn pair_double<T: Shape>(p: &Pair<T>) -> u32 { p.double() }
pub fn use_all(s: Sq) -> u32 { total(&s, &s) + name_id(&s) }
pub fn largest<T: PartialOrd + Clone>(xs: &[T], m: T) -> T { if xs[0] > m { xs[0].clone() } else { m } }
pub trait Sink { fn put<B: Clone>(&self, b: B) -> u32; }
pub fn put_all<S: Sink>(s: &S) -> u32 { s.put(1u8) }
pub fn pair_total<T: Shape>(p: &Pair<T>) -> u32 { total(p, p) }
pub fn count_down<T: Shape>(x: &T, n: u32) -> u32 { if n == 0 { x.area() } else { count_down(x, n - 1) } }

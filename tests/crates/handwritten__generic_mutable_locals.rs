// Mutable locals of types with generic parameters: the allocators of their cells are an
// allocation record parameter, which generic callers build from theirs (at the callees' type
// arguments) and concrete callers from the locale's allocators.
pub fn keep<T: Copy>(a: T) -> Option<T> {
    let mut x = a;
    x = a;
    let mut v: Option<T> = None;
    v = Some(x);
    v
}
pub fn keep_twice<U: Copy>(a: U) -> Option<U> { let _ = keep(a); keep(a) }
pub fn keep_pair<U: Copy>(a: U) -> Option<(U, U)> { keep((a, a)) }
pub fn keep_u32(a: u32) -> Option<u32> { keep(a) }
pub fn count<T: Copy>(a: T, n: u32) -> T {
    let mut x = a;
    x = a;
    if n == 0 { x } else { count(x, n - 1) }
}

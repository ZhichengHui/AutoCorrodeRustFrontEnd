// Generic functions called with a function item or a closure for an `Fn` type parameter (a function value), and with a mutable local of a generic type (an allocation record).
pub fn apply<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 { f(x) + 1 }
pub fn twice(x: u32) -> u32 { x * 2 }
pub fn use_item(x: u32) -> u32 { apply(twice, x) }
pub fn use_closure(x: u32, k: u32) -> u32 { apply(|y| y + k, x) }
pub fn use_ref<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 { f(x) }
pub fn use_ref_item(x: u32) -> u32 { use_ref(&twice, x) }
pub fn swap_tmp<T: Copy>(a: &mut T, b: &mut T) { let mut t = *a; t = t; *a = *b; *b = t; }
pub fn use_swap(mut a: u32, mut b: u32) -> u32 { swap_tmp(&mut a, &mut b); a }
// an external generic function called in a function with an `Fn`-bounded parameter of the same index
pub fn fill<F: Fn(u32) -> u32>(v: &mut Vec<u32>, f: F) { v.resize(3, f(0)); }

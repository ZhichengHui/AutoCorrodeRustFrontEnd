// Recursive groups of generic functions. A group is one HOL definition, in which each member is
// used at one type: mutual recursion that renames the type parameters consistently is defined;
// a call within the group at other type arguments (polymorphic recursion), directly or through
// another member, is a placeholder, also where it would make the allocation records of mutable
// locals grow without bound.
pub fn even<T: Copy>(x: T, n: u32) -> bool {
    if n == 0 { true } else { odd(x, n - 1) }
}

pub fn odd<U: Copy>(x: U, n: u32) -> bool {
    if n == 0 { false } else { even(x, n - 1) }
}

pub fn wrap<T: Clone>(x: T, n: u32) -> u32 {
    if n == 0 { 0 } else { unwrap_vec(vec![x], n - 1) }
}

pub fn unwrap_vec<T: Clone>(x: Vec<T>, n: u32) -> u32 {
    if n == 0 { 0 } else { wrap(x, n - 1) }
}

pub fn pair_up<T: Copy>(x: T, n: u32) -> T {
    let mut y = x;
    if n > 0 {
        y = pair_down((y, y), n - 1).0;
    }
    y
}

pub fn pair_down<T: Copy>(x: T, n: u32) -> T {
    let mut z = x;
    if n > 0 {
        z = pair_up(z, n - 1);
    }
    z
}

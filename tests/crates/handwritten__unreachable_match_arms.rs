// Match arms rustc finds unreachable (lint `unreachable_patterns`) are not translated: a final
// wildcard after arms for all variants, also for one-variant enums and pairs; arms with guards
// do not cover later arms, and a reachable wildcard stays.

pub enum One {
    A(u32),
}

pub enum Two {
    A,
    B(u32),
}

pub enum Unit {
    Only,
}

#[allow(unreachable_patterns)]
pub fn one(x: One) -> u32 {
    match x {
        One::A(n) => n,
        _ => 0,
    }
}

#[allow(unreachable_patterns)]
pub fn two(x: Two) -> u32 {
    match x {
        Two::A => 1,
        Two::B(n) => n,
        _ => 0,
    }
}

#[allow(unreachable_patterns)]
pub fn unit(x: Unit) -> bool {
    match x {
        Unit::Only => true,
        _ => false,
    }
}

pub fn guarded(x: Two) -> u32 {
    match x {
        Two::B(n) if n > 3 => n,
        Two::B(_) => 2,
        Two::A => 1,
    }
}

pub fn reachable(x: Two) -> u32 {
    match x {
        Two::A => 1,
        _ => 0,
    }
}

#[allow(unreachable_patterns)]
pub fn pair(x: One, y: One) -> u32 {
    match (x, y) {
        (One::A(a), One::A(b)) => a + b,
        _ => 0,
    }
}

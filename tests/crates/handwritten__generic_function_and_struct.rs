pub struct W<T> { pub v: T } pub fn id<T>(x: T) -> T { x } pub fn f(x: u32) -> u32 { let w = W { v: x }; id(w.v) }

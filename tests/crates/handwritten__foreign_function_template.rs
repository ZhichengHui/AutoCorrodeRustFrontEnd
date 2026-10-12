unsafe extern "C" { fn c_abs(x: i32) -> i32; } pub fn f(x: i32) -> i32 { unsafe { c_abs(x) } }

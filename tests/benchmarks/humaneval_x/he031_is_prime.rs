// HumanEval-X Rust/31 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn is_prime(n:i32) -> bool{


    if n < 2{
    return false;
}
for k in 2..n-1 {
    if n % k == 0{
        return false;
    }
}
return true;

}


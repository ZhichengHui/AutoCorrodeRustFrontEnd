// HumanEval-X Rust/13 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn greatest_common_divisor(mut a:i32,mut b:i32) -> i32{


    while b > 0 {
        (a, b) = (b, a % b);
    }
    return a;
}



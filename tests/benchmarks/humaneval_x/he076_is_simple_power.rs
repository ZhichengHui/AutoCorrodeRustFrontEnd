// HumanEval-X Rust/76 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn is_simple_power(x:i32, n:i32) -> bool{


    let mut p: i32 = 1;
    let mut count: i32 = 0;

    while p <= x && count < 100 {
        if p == x {
            return true;
        };
        p = p * n;
        count += 1;
    }
    return false;
}


// HumanEval-X Rust/83 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn starts_one_ends(n:i32) -> i32{


    if n == 1 {
        return 1;
    };
    return 18 * i32::pow(10, (n - 2) as u32);
}


// HumanEval-X Rust/138 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn is_equal_to_sum_even(n: i32) -> bool {


    if n % 2 == 0 && n >= 8 {
        return true;
    }
    return false;
}


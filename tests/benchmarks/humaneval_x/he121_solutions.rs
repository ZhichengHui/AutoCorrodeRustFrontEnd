// HumanEval-X Rust/121 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn solutions(lst: Vec<i32>) -> i32 {


    let mut sum = 0;
    for (indx, elem) in lst.iter().enumerate() {
        if indx % 2 == 0 {
            if elem % 2 == 1 {
                sum += elem;
            }
        }
    }
    return sum;
}


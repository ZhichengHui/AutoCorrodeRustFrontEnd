// HumanEval-X Rust/85 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn add_even_odd(lst: Vec<i32>) -> i32{


    let mut sum: i32 = 0;

    for (indx, elem) in lst.iter().enumerate() {
        if indx % 2 == 1 {
            if elem % 2 == 0 {
                sum += elem
            }
        }
    }
    return sum;
}


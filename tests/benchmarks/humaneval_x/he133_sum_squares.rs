// HumanEval-X Rust/133 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn sum_squares(lst: Vec<f32>) -> i32 {


    let mut sum: f32 = 0.0;
    for i in 0..lst.len() {
        sum = sum + (lst[i].ceil() * lst[i].ceil());
    }
    sum as i32
}


// HumanEval-X Rust/122 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn add_elements(arr: Vec<i32>, k: i32) -> i32 {


    let mut sum = 0;
    for i in 0..k {
        if arr[i as usize] >= -99 && arr[i as usize] <= 99 {
            sum += arr[i as usize];
        }
    }
    sum
}


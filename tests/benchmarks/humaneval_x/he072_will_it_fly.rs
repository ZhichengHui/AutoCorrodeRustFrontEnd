// HumanEval-X Rust/72 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn will_it_fly(q:Vec<i32>, w:i32) -> bool{


    if q.iter().sum::<i32>() > w {
        return false;
    }
    let mut i = 0;
    let mut j = q.len() - 1;

    while i < j {
        if q[i] != q[j] {
            return false;
        }
        i += 1;
        j -= 1;
    }
    return true;
}


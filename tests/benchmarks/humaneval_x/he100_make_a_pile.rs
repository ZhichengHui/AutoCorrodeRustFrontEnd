// HumanEval-X Rust/100 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn make_a_pile(n:i32) -> Vec<i32>{


    let mut out: Vec<i32> = vec![n];

    for i in 1..n {
        out.push(out[out.len() - 1] + 2);
    }

    return out;
}


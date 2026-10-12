// HumanEval-X Rust/60 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn sum_to_n(n: i32) -> i32 {


    n*(n+1)/2
}


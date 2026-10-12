// HumanEval-X Rust/42 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn incr_list(l:Vec<i32>) -> Vec<i32>{


    return l.into_iter().map(|n:i32| n + 1).collect();
}


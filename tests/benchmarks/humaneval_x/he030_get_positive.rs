// HumanEval-X Rust/30 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn get_positive(numbers:Vec<i32>) -> Vec<i32>{


    return numbers.into_iter().filter(|n| n.is_positive()).collect();

}


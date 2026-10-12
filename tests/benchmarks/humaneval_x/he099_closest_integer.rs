// HumanEval-X Rust/99 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn closest_integer(value:&str) -> i32 {


    return value.parse::<f64>().unwrap().round() as i32;
}


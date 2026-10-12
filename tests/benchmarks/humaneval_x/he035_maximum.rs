// HumanEval-X Rust/35 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn maximum(nmbs:Vec<i32>) -> i32{


    return *nmbs.iter().max().unwrap();
 }



// HumanEval-X Rust/58 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn common(l1:Vec<i32>, l2:Vec<i32>) -> Vec<i32>{


let mut res:Vec<i32> = l1.into_iter().filter(|n:&i32| l2.contains(n)).collect();
res.sort();
return res;
}


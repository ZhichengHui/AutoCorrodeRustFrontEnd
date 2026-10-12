// HumanEval-X Rust/66 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn digitSum(s:&str) -> i32{


    return s.chars().into_iter().filter(|c:&char| c.is_uppercase()).map(|c:char| c as i32).sum();
}


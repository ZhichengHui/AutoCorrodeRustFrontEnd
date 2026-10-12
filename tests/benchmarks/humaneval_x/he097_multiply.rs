// HumanEval-X Rust/97 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn multiply(a:i32, b:i32) -> i32{


    return (i32::abs(a) % 10) * (i32::abs(b) % 10);
}


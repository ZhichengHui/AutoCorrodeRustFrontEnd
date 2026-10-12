// HumanEval-X Rust/45 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn triangle_area(a:i32, h:i32) -> f64{


    return (a * h) as f64 / 2.0;
}


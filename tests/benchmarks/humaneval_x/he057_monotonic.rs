// HumanEval-X Rust/57 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn monotonic( l:Vec<i32>) -> bool{


    let mut l1:Vec<i32> = l.clone();
    let mut l2:Vec<i32> = l.clone();
    l2.sort(); l2.reverse();
    l1.sort();

    if  l == l1 || l == l2 {return true}
    return false;

}


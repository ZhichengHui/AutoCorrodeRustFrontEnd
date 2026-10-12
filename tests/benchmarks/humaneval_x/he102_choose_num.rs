// HumanEval-X Rust/102 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn choose_num(x:i32, y:i32) -> i32{


    if y < x {
        return -1;
    }
    if y == x && y % 2 == 1 {
        return -1;
    }
    if y % 2 == 1 {
        return y - 1;
    }
    return y;
}


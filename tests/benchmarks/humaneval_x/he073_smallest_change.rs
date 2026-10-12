// HumanEval-X Rust/73 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn smallest_change(arr:Vec<i32>) -> i32{


    let mut ans: i32 = 0;
    for i in 0..arr.len() / 2 {
        if arr[i] != arr[arr.len() - i - 1] {
            ans += 1
        }
    }
    return ans;
}


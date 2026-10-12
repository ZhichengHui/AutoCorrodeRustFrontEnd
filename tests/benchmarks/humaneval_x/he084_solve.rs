// HumanEval-X Rust/84 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn solve(n:i32) -> String{


    let sum: i32 = n
        .to_string()
        .chars()
        .into_iter()
        .fold(0, |acc, c| acc + c.to_digit(10).unwrap() as i32);
    return format!("{sum:b}");
}


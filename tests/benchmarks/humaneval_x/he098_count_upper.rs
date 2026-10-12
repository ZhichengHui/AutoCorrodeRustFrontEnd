// HumanEval-X Rust/98 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn count_upper(s:&str) -> i32 {


    let uvowel: &str = "AEIOU";
    let mut count: i32 = 0;

    for (indx, elem) in s.chars().into_iter().enumerate() {
        if indx % 2 == 0 {
            if uvowel.contains(elem) {
                count += 1;
            }
        }
    }
    return count;
}


// HumanEval-X Rust/91 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn is_bored(s:&str) -> i32 {


    let mut count = 0;
    let regex = Regex::new(r"[.?!]\s*").expect("Invalid regex");
    let sqn: Vec<&str> = regex.split(s).into_iter().collect();
    for s in sqn {
        if s.starts_with("I ") {
            count += 1;
        }
    }
    return count;
}


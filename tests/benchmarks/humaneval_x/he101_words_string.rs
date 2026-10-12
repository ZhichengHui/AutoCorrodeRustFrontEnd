// HumanEval-X Rust/101 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn words_string(s:&str) -> Vec<String> {


    return s
        .to_string()
        .split(|c: char| c == ',' || c.is_whitespace())
        .into_iter()
        .filter(|x| x != &"")
        .map(|x| x.to_string())
        .collect();
}


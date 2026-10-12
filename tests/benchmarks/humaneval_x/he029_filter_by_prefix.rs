// HumanEval-X Rust/29 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn filter_by_prefix(strings:Vec<String>, prefix:String)-> Vec<String>{


    return strings.into_iter().filter(|s| s.starts_with(&prefix)).collect();
}


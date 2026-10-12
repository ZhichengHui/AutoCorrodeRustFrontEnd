// HumanEval-X Rust/7 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn filter_by_substring(strings: Vec<String>, substring:String) -> Vec<String>{

    return strings.iter().filter(|x:&&String| x.contains(&substring)).map(String::from).collect();
}


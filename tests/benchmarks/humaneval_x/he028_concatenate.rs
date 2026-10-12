// HumanEval-X Rust/28 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn concatenate(strings:Vec<String>) -> String{


    return strings.iter().fold(String::new(),|res: String, x:&String| res + &x.to_string());

}


// HumanEval-X Rust/15 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn string_sequence(n:i32) -> String{


    let mut res:String = String::new();

    for number in 0..n + 1{
        res = res + &number.to_string() + " ";
    }
    
    return res.trim_end().to_string();

}


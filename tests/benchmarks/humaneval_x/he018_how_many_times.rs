// HumanEval-X Rust/18 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn how_many_times(string: String, substring:String) -> i32{


    let mut times:i32 = 0;

    for i in 0..(string.len() as i32 - substring.len() as i32 + 1){
        if string.get(i as usize..(i + substring.len() as i32) as usize).unwrap().to_string() == substring {
            times += 1;
        }    
    }
    return times;
}


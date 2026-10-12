// HumanEval-X Rust/9 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn rolling_max(numbers:Vec<i32>) -> Vec<i32>{

    let mut running_max :Option<i32> = None;
    let mut result:Vec<i32> = vec![];

    for n in numbers{
        if running_max == None {
            running_max = Some(n);

        }else{
            running_max = max(running_max, Some(n));
        }

        result.push(running_max.unwrap());
    }
    return result;

}


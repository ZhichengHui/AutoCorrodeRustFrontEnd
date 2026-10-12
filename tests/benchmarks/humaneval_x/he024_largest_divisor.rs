// HumanEval-X Rust/24 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn largest_divisor(n:i32) -> i32{


    let mut res:i32 = 0;
    let sqn = 1..n;
    
    for i in sqn.rev(){
        if n % i == 0 {
            res = i;
            break;
        }
    }

    return res;
}


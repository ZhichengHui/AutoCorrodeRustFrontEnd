// HumanEval-X Rust/44 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn change_base(x:i32, base:i32) -> String{


    let mut ret:String = "".to_string();
    let mut x1 = x;

    while  x1 > 0{
        ret = (x1 % base).to_string() + &ret;
        x1 = x1 / base;
    }
    return ret;
}



use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn derivative(xs:Vec<i32>) -> Vec<i32>{


    let mut res:Vec<i32> =vec![];
    for i in 1..xs.len(){
        res.push(i as i32 * xs.get(i).unwrap());
    }
    return res;

} 


use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn maximum_120(arr: Vec<i32>, k: i32) -> Vec<i32> {


    let mut arr = arr;
    arr.sort();
    let mut arr_res: Vec<i32> = arr.iter().rev().take(k as usize).cloned().collect();
    arr_res.sort();
    return arr_res;
}

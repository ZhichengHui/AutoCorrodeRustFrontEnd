
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn can_arrange(arr: Vec<i32>) -> i32 {


    let mut max: i32 = -1;
    for i in 0..arr.len() {
        if arr[i] <= i as i32 {
            max = i as i32;
        }
    }
    max
}


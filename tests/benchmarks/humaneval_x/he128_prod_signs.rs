
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn prod_signs(arr: Vec<i32>) -> i32 {


    if arr.is_empty() {
        return -32768;
    }
    let mut sum = 0;
    let mut prods = 1;
    for i in arr {
        sum += i.abs();
        if i == 0 {
            prods = 0;
        }
        if i < 0 {
            prods = -prods;
        }
    }
    sum * prods
}


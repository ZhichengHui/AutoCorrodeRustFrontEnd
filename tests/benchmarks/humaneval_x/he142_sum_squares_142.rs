
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn sum_squares_142(lst: Vec<i32>) -> i32 {


    let mut sum = 0;
    for i in 0..lst.len() {
        if i % 3 == 0 {
            sum += lst[i] * lst[i];
        } else if i % 4 == 0 {
            sum += lst[i] * lst[i] * lst[i];
        } else {
            sum += lst[i];
        }
    }
    return sum;
}

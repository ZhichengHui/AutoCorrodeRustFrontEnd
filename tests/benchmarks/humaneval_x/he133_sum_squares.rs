
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn sum_squares(lst: Vec<f32>) -> i32 {


    let mut sum: f32 = 0.0;
    for i in 0..lst.len() {
        sum = sum + (lst[i].ceil() * lst[i].ceil());
    }
    sum as i32
}


use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn double_the_difference(lst: Vec<f32>) -> i64 {


    let mut sum: i64 = 0;
    for i in 0..lst.len() {
        if (lst[i] - lst[i].round()).abs() < 1e-4 {
            if lst[i] > 0.0 && (lst[i].round() as i64) % 2 == 1 {
                sum += (lst[i].round() as i64) * (lst[i].round() as i64);
            }
        }
    }
    return sum;
}

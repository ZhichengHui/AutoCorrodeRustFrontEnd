
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn intersection(interval1: Vec<i32>, interval2: Vec<i32>) -> String {


    let inter1 = std::cmp::max(interval1[0], interval2[0]);
    let inter2 = std::cmp::min(interval1[1], interval2[1]);
    let l = inter2 - inter1;
    if l < 2 {
        return "NO".to_string();
    }
    for i in 2..l {
        if l % i == 0 {
            return "NO".to_string();
        }
    }
    return "YES".to_string();
}

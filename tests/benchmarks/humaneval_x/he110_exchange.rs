
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn exchange(lst1:Vec<i32>, lst2:Vec<i32>) -> String{


    let mut num = 0;
    for i in 0..lst1.len() {
        if lst1[i] % 2 == 0 {
            num += 1;
        }
    }
    for i in 0..lst2.len() {
        if lst2[i] % 2 == 0 {
            num += 1;
        }
    }
    if num >= lst1.len() {
        return "YES".to_string();
    }
    return "NO".to_string();
}

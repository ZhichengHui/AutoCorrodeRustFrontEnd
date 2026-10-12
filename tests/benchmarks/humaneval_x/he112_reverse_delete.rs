
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn reverse_delete(s:&str, c:&str) -> Vec<String> {


    let mut n = String::new();
    for i in 0..s.len() {
        if !c.contains(s.chars().nth(i).unwrap()) {
            n.push(s.chars().nth(i).unwrap());
        }
    }
    if n.len() == 0 {
        return vec![n, "True".to_string()];
    }
    let w: String = n.chars().rev().collect();
    if w == n {
        return vec![n, "True".to_string()];
    }
    return vec![n, "False".to_string()];
}

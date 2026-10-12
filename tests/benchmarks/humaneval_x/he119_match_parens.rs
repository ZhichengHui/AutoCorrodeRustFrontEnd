
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn match_parens(lst: Vec<&str>) -> &str {


    let l1 = lst[0].to_string() + lst[1];
    let mut count = 0;
    let mut can = true;
    for i in 0..l1.len() {
        if l1.chars().nth(i).unwrap() == '(' {
            count += 1;
        }
        if l1.chars().nth(i).unwrap() == ')' {
            count -= 1;
        }
        if count < 0 {
            can = false;
        }
    }
    if count != 0 {
        return "No";
    }
    if can == true {
        return "Yes";
    }
    let l1 = lst[1].to_string() + lst[0];
    let mut can = true;
    for i in 0..l1.len() {
        if l1.chars().nth(i).unwrap() == '(' {
            count += 1;
        }
        if l1.chars().nth(i).unwrap() == ')' {
            count -= 1;
        }
        if count < 0 {
            can = false;
        }
    }
    if can == true {
        return "Yes";
    }
    return "No";
}

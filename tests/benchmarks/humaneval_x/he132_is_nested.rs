
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn is_nested(str: &str) -> bool {


    let mut count = 0;
    let mut maxcount = 0;
    for i in 0..str.len() {
        if str.chars().nth(i).unwrap() == '[' {
            count += 1;
        }
        if str.chars().nth(i).unwrap() == ']' {
            count -= 1;
        }
        if count < 0 {
            count = 0;
        }
        if count > maxcount {
            maxcount = count;
        }
        if count <= maxcount - 2 {
            return true;
        }
    }
    return false;
}

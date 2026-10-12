
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn cycpattern_check(a: &str, b: &str) -> bool {


    for i in 0..b.len() {
        let rotate = format!("{}{}", &b[i..], &b[..i]);
        if a.contains(&rotate) {
            return true;
        }
    }
    false
}


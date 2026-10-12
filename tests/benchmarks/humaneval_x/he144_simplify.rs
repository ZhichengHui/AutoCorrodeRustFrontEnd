
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn simplify(x: &str, n: &str) -> bool {


    let mut a = 0;
    let mut b = 0;
    let mut c = 0;
    let mut d = 0;
    let mut i = 0;
    for i in 0..x.len() {
        if x.chars().nth(i).unwrap() == '/' {
            a = x
                .chars()
                .take(i)
                .collect::<String>()
                .parse::<i32>()
                .unwrap();
            b = x
                .chars()
                .skip(i + 1)
                .collect::<String>()
                .parse::<i32>()
                .unwrap();
        }
    }
    for i in 0..n.len() {
        if n.chars().nth(i).unwrap() == '/' {
            c = n
                .chars()
                .take(i)
                .collect::<String>()
                .parse::<i32>()
                .unwrap();
            d = n
                .chars()
                .skip(i + 1)
                .collect::<String>()
                .parse::<i32>()
                .unwrap();
        }
    }
    if (a * c) % (b * d) == 0 {
        return true;
    }
    return false;
}

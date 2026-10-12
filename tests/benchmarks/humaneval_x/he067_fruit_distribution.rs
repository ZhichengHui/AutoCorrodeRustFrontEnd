
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn fruit_distribution(s:&str, n:i32) -> i32 {


    let sub:i32 = s.split_ascii_whitespace().into_iter().filter(|c| c.parse::<i32>().is_ok()).map(|c| c.parse::<i32>().unwrap()).sum();
    return n-sub;
}


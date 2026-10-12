
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn same_chars(str1:&str, str2:&str) -> bool{


    let mut v1:Vec<char> = str1.chars().into_iter().collect();
    v1.sort();
    v1.dedup();

    let mut v2:Vec<char> = str2.chars().into_iter().collect();
    v2.sort();
    v2.dedup();

    return v1 == v2;
}

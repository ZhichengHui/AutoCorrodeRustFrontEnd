
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn count_distinct_characters(str:String) -> i32{


    let res:HashSet<char> = str.chars().into_iter().map(|x:char| x.to_ascii_lowercase()).collect();
    return res.len() as i32;
}

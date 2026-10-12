
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn closest_integer(value:&str) -> i32 {


    return value.parse::<f64>().unwrap().round() as i32;
}

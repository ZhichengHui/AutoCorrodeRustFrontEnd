
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn special_factorial(n: i32) -> i64 {


    let mut fact = 1;
    let mut bfact: i64 = 1;
    for i in 1..=n {
        fact = fact * i;
        bfact = bfact * fact as i64;
    }
    bfact
}


use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn hex_key(num:&str) -> i32{


    let primes: Vec<&str> = vec!["2", "3", "5", "7", "B", "D"];
    let mut total: i32 = 0;
    for i in 0..num.len() {
        if primes.contains(&num.get(i..i + 1).unwrap()) {
            total += 1;
        }
    }
    return total;
}

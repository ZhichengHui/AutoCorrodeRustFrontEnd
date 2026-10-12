
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn get_odd_collatz(n: i32) -> Vec<i32> {


    let mut out = vec![1];
    let mut n = n;
    while n != 1 {
        if n % 2 == 1 {
            out.push(n);
            n = n * 3 + 1;
        } else {
            n = n / 2;
        }
    }
    out.sort();
    out
}


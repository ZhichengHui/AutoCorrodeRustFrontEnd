
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn f(n:i32) -> Vec<i32>{


    let mut sum: i32 = 0;
    let mut prod: i32 = 1;
    let mut out: Vec<i32> = vec![];

    for i in 1..n + 1 {
        sum += i;
        prod *= i;

        if i % 2 == 0 {
            out.push(prod);
        } else {
            out.push(sum)
        };
    }
    return out;
}


use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn tri(n: i32) -> Vec<i32> {


    let mut out = vec![1, 3];
    if n == 0 {
        return vec![1];
    }
    for i in 2..=n {
        if i % 2 == 0 {
            out.push(1 + i / 2);
        } else {
            out.push(out[(i - 1) as usize] + out[(i - 2) as usize] + 1 + (i + 1) / 2);
        }
    }
    out
}

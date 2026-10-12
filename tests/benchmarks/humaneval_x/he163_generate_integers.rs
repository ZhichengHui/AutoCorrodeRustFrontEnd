
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn generate_integers(a: i32, b: i32) -> Vec<i32> {


    let mut a = a;
    let mut b = b;
    let mut m;

    if b < a {
        m = a;
        a = b;
        b = m;
    }

    let mut out = vec![];
    for i in a..=b {
        if i < 10 && i % 2 == 0 {
            out.push(i);
        }
    }
    out
}

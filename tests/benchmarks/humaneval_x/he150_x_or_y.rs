
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn x_or_y(n: i32, x: i32, y: i32) -> i32 {


    let mut isp = true;
    if n < 2 {
        isp = false;
    }
    for i in 2..=n / 2 {
        if n % i == 0 {
            isp = false;
        }
    }
    if isp {
        return x;
    }
    return y;
}

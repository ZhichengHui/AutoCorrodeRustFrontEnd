
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn valid_date(date: &str) -> bool {


    let mut mm = 0;
    let mut dd = 0;
    let mut yy = 0;
    let mut i = 0;
    if date.len() != 10 {
        return false;
    }
    for i in 0..10 {
        if i == 2 || i == 5 {
            if date.chars().nth(i).unwrap() != '-' {
                return false;
            }
        } else if date.chars().nth(i).unwrap() < '0' || date.chars().nth(i).unwrap() > '9' {
            return false;
        }
    }
    mm = date[0..2].parse::<i32>().unwrap();
    dd = date[3..5].parse::<i32>().unwrap();
    yy = date[6..10].parse::<i32>().unwrap();
    if mm < 1 || mm > 12 {
        return false;
    }
    if dd < 1 || dd > 31 {
        return false;
    }
    if dd == 31 && (mm == 4 || mm == 6 || mm == 9 || mm == 11 || mm == 2) {
        return false;
    }
    if dd == 30 && mm == 2 {
        return false;
    }
    return true;
}


use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn eat(number: i32, need: i32, remaining: i32) -> Vec<i32> {


    if need > remaining {
        return vec![number + remaining, 0];
    }
    return vec![number + need, remaining - need];
}

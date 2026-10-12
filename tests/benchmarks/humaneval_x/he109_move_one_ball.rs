
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn move_one_ball(arr:Vec<i32>) -> bool{


    let mut num = 0;
    if arr.len() == 0 {
        return true;
    }
    for i in 1..arr.len() {
        if arr[i] < arr[i - 1] {
            num += 1;
        }
    }
    if arr[arr.len() - 1] > arr[0] {
        num += 1;
    }
    if num < 2 {
        return true;
    }
    return false;
}

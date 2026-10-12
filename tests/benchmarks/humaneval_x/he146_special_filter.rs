
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn special_filter(nums: Vec<i32>) -> i32 {


    let mut num = 0;
    for i in 0..nums.len() {
        if nums[i] > 10 {
            let w = nums[i].to_string();
            if w.chars().nth(0).unwrap().to_digit(10).unwrap() % 2 == 1
                && w.chars().last().unwrap().to_digit(10).unwrap() % 2 == 1
            {
                num += 1;
            }
        }
    }
    num
}

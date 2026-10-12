
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn count_nums(n:Vec<i32>) -> i32{


    let mut num: i32 = 0;

    for nmbr in n {
        if nmbr > 0 {
            num += 1;
        } else {
            let mut sum: i32 = 0;
            let mut w: i32;
            w = i32::abs(nmbr);

            while w >= 10 {
                sum += w % 10;
                w = w / 10;
            }
            sum -= w;
            if sum > 0 {
                num += 1;
            }
        }
    }
    return num;
}

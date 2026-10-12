
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn get_row(lst:Vec<Vec<i32>>, x:i32) -> Vec<Vec<i32>>{


    let mut out: Vec<Vec<i32>> = vec![];
    for (indxi, elem1) in lst.iter().enumerate() {
        for (indxj, _) in elem1.iter().rev().enumerate() {
            if lst[indxi][indxj] == x {
                out.push(vec![indxi as i32, indxj as i32]);
            }
        }
    }
    return out;
}

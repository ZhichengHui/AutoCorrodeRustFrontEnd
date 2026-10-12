
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn sorted_list_sum(lst: Vec<&str>) -> Vec<&str> {


    let mut out: Vec<&str> = Vec::new();
    for i in 0..lst.len() {
        if lst[i].len() % 2 == 0 {
            out.push(lst[i]);
        }
    }
    out.sort();
    for i in 0..out.len() {
        for j in 1..out.len() {
            if out[j].len() < out[j - 1].len() {
                let mid = out[j];
                out[j] = out[j - 1];
                out[j - 1] = mid;
            }
        }
    }
    return out;
}

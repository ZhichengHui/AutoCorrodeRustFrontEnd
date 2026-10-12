
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn largest_smallest_integers(lst: Vec<i32>) -> Vec<i32> {


    let mut maxneg = 0;
    let mut minpos = 0;
    for i in 0..lst.len() {
        if lst[i] < 0 && (maxneg == 0 || lst[i] > maxneg) {
            maxneg = lst[i];
        }
        if lst[i] > 0 && (minpos == 0 || lst[i] < minpos) {
            minpos = lst[i];
        }
    }
    vec![maxneg, minpos]
}

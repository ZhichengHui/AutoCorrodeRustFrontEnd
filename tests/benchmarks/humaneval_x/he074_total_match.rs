
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn total_match(lst1:Vec<&str>, lst2:Vec<&str>) -> Vec<String>{


    let total_1: usize = lst1
        .iter()
        .fold(0, |acc: usize, str: &&str| acc + str.chars().count());
    let total_2: usize = lst2
        .iter()
        .fold(0, |acc: usize, str: &&str| acc + str.chars().count());

    if total_1 <= total_2 {
        return lst1.into_iter().map(|x| x.to_string()).collect();
    } else {
        return lst2.into_iter().map(|x| x.to_string()).collect();
    }
}

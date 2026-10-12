
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn file_name_check(file_name: &str) -> &str {


    let mut numdigit = 0;
    let mut numdot = 0;
    if file_name.len() < 5 {
        return "No";
    }
    let w = file_name.chars().nth(0).unwrap();
    if w < 'A' || (w > 'Z' && w < 'a') || w > 'z' {
        return "No";
    }
    let last = &file_name[file_name.len() - 4..];
    if last != ".txt" && last != ".exe" && last != ".dll" {
        return "No";
    }
    for c in file_name.chars() {
        if c >= '0' && c <= '9' {
            numdigit += 1;
        }
        if c == '.' {
            numdot += 1;
        }
    }
    if numdigit > 3 || numdot != 1 {
        return "No";
    }
    return "Yes";
}

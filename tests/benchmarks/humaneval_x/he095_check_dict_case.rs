
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn check_dict_case(dict:HashMap<&str, &str>) -> bool{


    if dict.is_empty() {
        return false;
    }
    let string_lower: fn(str: &str) -> bool = |str: &str| {
        return str.chars().into_iter().all(|c| c.is_ascii_lowercase());
    };
    let string_upper: fn(str: &str) -> bool = |str: &str| {
        return str.chars().into_iter().all(|c| c.is_ascii_uppercase());
    };

    let lower: bool = dict.keys().into_iter().all(|str| string_lower(str));
    let upper: bool = dict.keys().into_iter().all(|str| string_upper(str));
    return lower || upper;
}

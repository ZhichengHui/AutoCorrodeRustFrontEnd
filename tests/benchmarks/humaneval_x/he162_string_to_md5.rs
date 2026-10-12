
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn string_to_md5(text: &str) -> String {


    if text.is_empty() {
        return "None".to_string();
    }

    let digest = md5::compute(text.as_bytes());
    return format!("{:x}", digest);
}

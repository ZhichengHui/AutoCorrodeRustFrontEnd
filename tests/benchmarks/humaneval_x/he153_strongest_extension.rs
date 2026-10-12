
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn strongest_extension(class_name: &str, extensions: Vec<&str>) -> String { 


    let mut strongest = "";
    let mut max = -1000;
    for i in 0..extensions.len() {
        let mut strength = 0;
        for j in 0..extensions[i].len() {
            let chr = extensions[i].chars().nth(j).unwrap();
            if chr >= 'A' && chr <= 'Z' {
                strength += 1;
            }
            if chr >= 'a' && chr <= 'z' {
                strength -= 1;
            }
        }
        if strength > max {
            max = strength;
            strongest = extensions[i];
        }
    }
    format!("{}.{}", class_name, strongest)
}

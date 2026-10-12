// HumanEval-X Rust/134 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn check_if_last_char_is_a_letter(txt: &str) -> bool {


    if txt.len() == 0 {
        return false;
    }
    let chr = txt.chars().last().unwrap();
    if chr < 'A' || (chr > 'Z' && chr < 'a') || chr > 'z' {
        return false;
    }
    if txt.len() == 1 {
        return true;
    }
    let chr = txt.chars().nth(txt.len() - 2).unwrap();
    if (chr >= 'A' && chr <= 'Z') || (chr >= 'a' && chr <= 'z') {
        return false;
    }
    true
}


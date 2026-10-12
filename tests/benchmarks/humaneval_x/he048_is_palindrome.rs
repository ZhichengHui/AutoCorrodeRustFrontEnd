// HumanEval-X Rust/48 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn is_palindrome(text: String) -> bool {


    let pr: String = text.chars().rev().collect();
    return pr == text;
}


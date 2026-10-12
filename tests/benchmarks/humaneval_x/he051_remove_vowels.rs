// HumanEval-X Rust/51 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn remove_vowels(text: &str) -> String {


    let vowels = "AEIOUaeiou";
    let mut out = String::new();
    for c in text.chars() {
        if !vowels.contains(c) {
            out.push(c);
        }
    }
    out
}


// HumanEval-X Rust/118 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn get_closest_vowel(word: &str) -> String {


    let vowels = "AEIOUaeiou";
    let mut out = "".to_string();
    for i in (1..word.len() - 1).rev() {
        if vowels.contains(word.chars().nth(i).unwrap()) {
            if !vowels.contains(word.chars().nth(i + 1).unwrap()) {
                if !vowels.contains(word.chars().nth(i - 1).unwrap()) {
                    out.push(word.chars().nth(i).unwrap());
                    return out;
                }
            }
        }
    }
    out
}


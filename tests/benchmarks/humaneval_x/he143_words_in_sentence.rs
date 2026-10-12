// HumanEval-X Rust/143 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn words_in_sentence(sentence: &str) -> String {


    let mut out = String::new();
    let mut current = String::new();
    let mut sentence = sentence.to_string();
    sentence.push(' ');

    for i in 0..sentence.len() {
        if sentence.chars().nth(i).unwrap() != ' ' {
            current.push(sentence.chars().nth(i).unwrap());
        } else {
            let mut isp = true;
            let l = current.len();
            if l < 2 {
                isp = false;
            }
            for j in 2..(l as f64).sqrt() as usize + 1 {
                if l % j == 0 {
                    isp = false;
                }
            }
            if isp {
                out.push_str(&current);
                out.push(' ');
            }
            current = String::new();
        }
    }
    if out.len() > 0 {
        out.pop();
    }
    out
}


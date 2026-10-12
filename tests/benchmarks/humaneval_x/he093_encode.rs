// HumanEval-X Rust/93 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn encode(message:&str) -> String{


    let mut res: String = String::new();
    let v: Vec<char> = "aeiouAEIOU".to_string().chars().into_iter().collect();
    let d: Vec<char> = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
        .to_string()
        .chars()
        .into_iter()
        .collect();

    for (indx, elem) in message.chars().into_iter().enumerate() {
        let mut c = elem.to_string();

        if v.contains(&elem) {
            let indx: usize = d.iter().position(|x| &elem == x).unwrap();
            c = d[indx + 2 as usize].to_string();
        }

        if elem.is_uppercase() {
            c = c.to_lowercase().to_string();
        } else {
            c = c.to_uppercase().to_string();
        }
        res.push_str(&c);
    }
    return res;
}


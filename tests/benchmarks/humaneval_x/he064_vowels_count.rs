// HumanEval-X Rust/64 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn vowels_count(s:&str) -> i32 {


    let vowels:&str = "aeiouAEIOU";
    let mut count:i32 = 0;

    for i in 0..s.len() {
       let c:char = s.chars().nth(i).unwrap();
       if vowels.contains(c){
        count += 1;
       } 
    }
    if s.chars().nth(s.len() -1).unwrap() == 'y' || s.chars().nth(s.len() -1).unwrap() == 'Y' {count+=1;}

    return count;
}


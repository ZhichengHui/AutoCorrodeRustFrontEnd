// HumanEval-X Rust/14 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn all_prefixes(string: String) -> Vec<String>{


   let mut res:Vec<String> = vec![];
   let mut res_str:String = String::new();

for c in string.chars(){
    res_str.push(c);
    res.push(res_str.clone());
}
return res;
}



// HumanEval-X Rust/40 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn triples_sum_to_zero(nmbs:Vec<i32>) -> bool{


    for i in 0.. nmbs.len(){
        for j in i + 1.. nmbs.len(){
            for k in j + 1.. nmbs.len(){
                if *nmbs.get(i).unwrap() + *nmbs.get(j).unwrap() + *nmbs.get(k).unwrap() == 0{
                    return true;
                }
            }
        }
    }
return false;

}


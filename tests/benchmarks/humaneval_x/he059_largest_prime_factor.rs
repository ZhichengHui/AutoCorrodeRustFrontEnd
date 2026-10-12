// HumanEval-X Rust/59 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn largest_prime_factor(n:i32) -> i32{


    let mut n1 = n.clone();
    for i in 2.. n1{
        while n1%i == 0 && n1>i{n1 = n1/i;}
    }
    return n1;
}


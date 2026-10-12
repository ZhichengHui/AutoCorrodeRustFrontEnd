// HumanEval-X Rust/96 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn count_up_to(n:i32) -> Vec<i32> {


    let mut primes: Vec<i32> = vec![];

    for i in 2..n {
        let mut is_prime: bool = true;

        for j in 2..i {
            if i % j == 0 {
                is_prime = false;
                break;
            }
        }
        if is_prime {
            primes.push(i);
        }
    }
    return primes;
}


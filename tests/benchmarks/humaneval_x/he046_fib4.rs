
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn fib4(n:i32) -> i32{


    let mut results:Vec<i32> = vec![0, 0, 2, 0];

    if n < 4 {
        return *results.get(n as usize).unwrap();
    }

    for _ in 4.. n + 1{
        results.push(results.get(results.len()-1).unwrap() + results.get(results.len()-2).unwrap()
         + results.get(results.len()-3).unwrap() + results.get(results.len()-4).unwrap());
        results.remove(0);
    }

    return *results.get(results.len()-1).unwrap();

    
}

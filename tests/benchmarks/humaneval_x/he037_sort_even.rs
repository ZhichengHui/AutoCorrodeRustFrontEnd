
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn sort_even(nmbs:Vec<i32>) -> Vec<i32>{


    let mut even = vec![];
    let mut out:Vec<i32> = vec![];

    for (indx,elem) in nmbs.iter().enumerate(){
        if indx%2 == 0{
            even.push(elem)
        }
    }
    even.sort();
    let mut indx_t:usize = 0;

    for i in 0..nmbs.len() {
        if i%2 == 0{
            if indx_t < even.len(){
                out.push(*even[indx_t]);
                indx_t += 1;
        }
        }else{
            out.push(nmbs[i]);
        }
        
    }
    return out;
}

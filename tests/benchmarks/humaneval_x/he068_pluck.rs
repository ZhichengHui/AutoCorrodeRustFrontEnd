
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn pluck(arr:Vec<i32>) -> Vec<i32> {


    let mut out:Vec<i32> = vec![];

    for i in 0.. arr.len(){
        if arr[i]%2 == 0 && (out.len() == 0 || arr[i]<out[0]){
        out = vec![arr[i], i as i32];
        }
       
    }
    return out;
}

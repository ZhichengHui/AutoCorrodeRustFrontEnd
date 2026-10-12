
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn longest(strings:Vec<String>) -> Option<String>{


    if strings.is_empty(){
        return None;
    }
    let mut max:i32 = 0;
    let mut res:String = String::new();

    for s in strings{
        if s.len() as i32 > max {
            res = s;
            max = res.len() as i32;
        }    
    }
     return Some(res);
}

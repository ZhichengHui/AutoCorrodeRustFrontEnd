
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn parse_music(music_string:String) -> Vec<i32>{



    let map = |x:&str| {match x {
        "o" => 4,
        "o|" => 2,
        ".|" =>  1,
        _ => 0
    } 
};
    return music_string.split(" ").map(|x:&str| map(&x.to_string())).filter(|x:&i32| x != &0).collect();
}


use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn compare(game: Vec<i32>, guess: Vec<i32>) -> Vec<i32> {


    let mut out: Vec<i32> = Vec::new();
    for i in 0..game.len() {
        out.push(i32::abs(game[i] - guess[i]));
    }
    return out;
}

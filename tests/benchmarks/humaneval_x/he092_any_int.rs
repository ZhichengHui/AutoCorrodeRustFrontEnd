
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn any_int(a:f64, b:f64, c:f64) -> bool{


    if a.fract() == 0.0 && b.fract() == 0.0 && c.fract() == 0.0 {
        return a + b == c || a + c == b || b + c == a;
    } else {
        return false;
    }
}

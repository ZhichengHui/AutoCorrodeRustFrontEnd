
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn factorize(n: i32) -> Vec<i32> {


    let mut n = n;
    let mut factors = vec![];
    let mut divisor = 2;
    while divisor * divisor <= n {
        while n % divisor == 0 {
            factors.push(divisor);
            n = n / divisor;
        }
        divisor = divisor + 1;
    }
    if n > 1 {
        factors.push(n);
    }
    factors
}

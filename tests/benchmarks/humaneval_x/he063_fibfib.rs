
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn fibfib(n:i32) -> i32{


    if n == 0 || n == 1{
        return 0;
    }
    if n == 2{
        return 1;
    }

    return fibfib(n-1) + fibfib(n-2) + fibfib(n-3);

}

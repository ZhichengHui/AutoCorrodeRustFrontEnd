// HumanEval-X Rust/55 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn fib(n:i32) -> i32{


    if n == 0{
        return 0;
    }
    if n == 1{
        return 1;
    }

    return fib(n-1) + fib(n-2);
}


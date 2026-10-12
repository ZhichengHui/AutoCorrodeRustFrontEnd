// HumanEval-X Rust/22 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn filter_integers(values: Vec<Box<dyn Any>>) -> Vec<i32> {


        let mut out: Vec<i32> = Vec::new();
        for value in values {
            if let Some(i) = value.downcast_ref::<i32>() {
                out.push(*i);
            }
        }
        out
    }


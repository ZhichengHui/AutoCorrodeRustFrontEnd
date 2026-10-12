// HumanEval-X Rust/0 (declaration + canonical solution)
#![allow(unused, deprecated)]

use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};



use std::any::{Any, TypeId};

fn has_close_elements(numbers:Vec<f32>, threshold: f32) -> bool{

    for i in 0..numbers.len(){
        for j in 1..numbers.len(){

            if i != j {
                let distance:f32 = numbers[i] - numbers[j];

            if distance.abs() < threshold{
                return true;
            }

            }
            
        }
    }

    return false;

}



use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn do_algebra(operato: Vec<&str>, operand: Vec<i32>) -> i32 {


    let mut operand: Vec<i32> = operand;
    let mut num: Vec<i32> = vec![];
    let mut posto: Vec<i32> = vec![];
    for i in 0..operand.len() {
        posto.push(i as i32);
    }
    for i in 0..operato.len() {
        if operato[i] == "**" {
            while posto[posto[i] as usize] != posto[i] {
                posto[i] = posto[posto[i] as usize];
            }
            while posto[posto[i + 1] as usize] != posto[i + 1] {
                posto[i + 1] = posto[posto[i + 1] as usize];
            }
            operand[posto[i] as usize] =
                operand[posto[i] as usize].pow(operand[posto[i + 1] as usize] as u32);
            posto[i + 1] = posto[i];
        }
    }
    for i in 0..operato.len() {
        if operato[i] == "*" || operato[i] == "//" {
            while posto[posto[i] as usize] != posto[i] {
                posto[i] = posto[posto[i] as usize];
            }
            while posto[posto[i + 1] as usize] != posto[i + 1] {
                posto[i + 1] = posto[posto[i + 1] as usize];
            }
            if operato[i] == "*" {
                operand[posto[i] as usize] =
                    operand[posto[i] as usize] * operand[posto[i + 1] as usize];
            } else {
                operand[posto[i] as usize] =
                    operand[posto[i] as usize] / operand[posto[i + 1] as usize];
            }
            posto[i + 1] = posto[i];
        }
    }
    for i in 0..operato.len() {
        if operato[i] == "+" || operato[i] == "-" {
            while posto[posto[i] as usize] != posto[i] {
                posto[i] = posto[posto[i] as usize];
            }
            while posto[posto[i + 1] as usize] != posto[i + 1] {
                posto[i + 1] = posto[posto[i + 1] as usize];
            }
            if operato[i] == "+" {
                operand[posto[i] as usize] =
                    operand[posto[i] as usize] + operand[posto[i + 1] as usize];
            } else {
                operand[posto[i] as usize] =
                    operand[posto[i] as usize] - operand[posto[i + 1] as usize];
            }
            posto[i + 1] = posto[i];
        }
    }
    operand[0]
}

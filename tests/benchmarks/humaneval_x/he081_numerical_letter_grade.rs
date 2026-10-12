
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn numerical_letter_grade(grades:Vec<f64>) -> Vec<String>{


    let mut res: Vec<String> = vec![];
    for (i, gpa) in grades.iter().enumerate() {
        if gpa == &4.0 {
            res.push("A+".to_string());
        } else if gpa > &3.7 {
            res.push("A".to_string());
        } else if gpa > &3.3 {
            res.push("A-".to_string());
        } else if gpa > &3.0 {
            res.push("B+".to_string());
        } else if gpa > &2.7 {
            res.push("B".to_string());
        } else if gpa > &2.3 {
            res.push("B-".to_string());
        } else if gpa > &2.0 {
            res.push("C+".to_string());
        } else if gpa > &1.7 {
            res.push("C".to_string());
        } else if gpa > &1.3 {
            res.push("C-".to_string());
        } else if gpa > &1.0 {
            res.push("D+".to_string());
        } else if gpa > &0.7 {
            res.push("D".to_string());
        } else if gpa > &0.0 {
            res.push("D-".to_string());
        } else {
            res.push("E".to_string());
        }
    }
    return res;
}

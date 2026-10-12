
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn get_matrix_triples(n: i32) -> i32 {


    let mut a = vec![];
    let mut sum = vec![vec![0, 0, 0]];
    let mut sum2 = vec![vec![0, 0, 0]];

    for i in 1..=n {
        a.push((i * i - i + 1) % 3);
        sum.push(sum[sum.len() - 1].clone());
        sum[i as usize][a[i as usize - 1] as usize] += 1;
    }

    for times in 1..3 {
        for i in 1..=n {
            sum2.push(sum2[sum2.len() - 1].clone());
            if i >= 1 {
                for j in 0..=2 {
                    sum2[i as usize][(a[i as usize - 1] + j) as usize % 3] +=
                        sum[i as usize - 1][j as usize];
                }
            }
        }
        sum = sum2.clone();
        sum2 = vec![vec![0, 0, 0]];
    }

    return sum[n as usize][0];
}

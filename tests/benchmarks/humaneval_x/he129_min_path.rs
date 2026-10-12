
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn min_path(grid: Vec<Vec<i32>>, k: i32) -> Vec<i32> {


    let mut out: Vec<i32> = vec![];
    let mut x = 0;
    let mut y = 0;
    let mut min: i32 = (grid.len() * grid.len()) as i32;
    for i in 0..grid.len() {
        for j in 0..grid[i].len() {
            if grid[i][j] == 1 {
                x = i;
                y = j;
            }
        }
    }
    if x > 0 && grid[x - 1][y] < min {
        min = grid[x - 1][y];
    }
    if x < grid.len() - 1 && grid[x + 1][y] < min {
        min = grid[x + 1][y];
    }
    if y > 0 && grid[x][y - 1] < min {
        min = grid[x][y - 1];
    }
    if y < grid.len() - 1 && grid[x][y + 1] < min {
        min = grid[x][y + 1];
    }
    let mut out = vec![];
    for i in 0..k {
        if i % 2 == 0 {
            out.push(1);
        } else {
            out.push(min);
        }
    }
    out
}

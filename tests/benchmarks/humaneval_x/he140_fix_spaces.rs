
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn fix_spaces(text: &str) -> String {


    let mut out = String::new();
    let mut spacelen = 0;
    for c in text.chars() {
        if c == ' ' {
            spacelen += 1;
        } else {
            if spacelen == 1 {
                out.push('_');
            }
            if spacelen == 2 {
                out.push_str("__");
            }
            if spacelen > 2 {
                out.push('-');
            }
            spacelen = 0;
            out.push(c);
        }
    }
    if spacelen == 1 {
        out.push('_');
    }
    if spacelen == 2 {
        out.push_str("__");
    }
    if spacelen > 2 {
        out.push('-');
    }
    out
}

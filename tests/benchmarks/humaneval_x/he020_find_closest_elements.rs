
use std::{slice::Iter, cmp::{max, self}, mem::replace, collections::{HashSet, HashMap}, ops::Index, ascii::AsciiExt};
use rand::Rng;
use regex::Regex;
use md5;
use std::any::{Any, TypeId};

fn find_closest_elements(numbers:Vec<f32>) -> (f32,f32){


    let mut closest_pair = (0.0,0.0);
    let mut distance:Option<f32> = None;

    for (idx, elem) in numbers.iter().enumerate(){
        for (idx2, elem2) in  numbers.iter().enumerate() {
            if idx != idx2 {
                if distance == None {
                    distance = Some((elem - elem2).abs());
                    if *elem < *elem2{
                        closest_pair = (*elem, *elem2);
                    }else{
                        closest_pair = (*elem2, *elem);
                    }

                }else{
                    let new_distance:f32= (elem - elem2).abs();
                    if new_distance < distance.unwrap(){
                        distance = Some(new_distance);

                        if *elem < *elem2{
                            closest_pair = (*elem, *elem2);
                        }else{
                            closest_pair = (*elem2, *elem);
                        }
                        
    
                    }
                }
            }
        }
    }
    return closest_pair;


}

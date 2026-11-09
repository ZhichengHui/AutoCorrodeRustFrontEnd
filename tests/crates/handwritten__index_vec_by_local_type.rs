use std::ops::{Index, IndexMut};

#[derive(Clone, Copy)]
pub struct Var(pub u32);

impl<T> Index<Var> for Vec<T> {
    type Output = T;
    fn index(&self, v: Var) -> &T {
        &self[v.0 as usize]
    }
}

impl<T> IndexMut<Var> for Vec<T> {
    fn index_mut(&mut self, v: Var) -> &mut T {
        &mut self[v.0 as usize]
    }
}

pub fn get(levels: &Vec<u32>, v: Var) -> u32 {
    levels[v]
}

pub fn set(levels: &mut Vec<u32>, v: Var, x: u32) {
    levels[v] = x;
}

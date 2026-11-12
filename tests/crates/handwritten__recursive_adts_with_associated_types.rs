// Mutually recursive ADTs with associated types of their type parameters in fields: the members
// of the group share the union of their associated types as extra type parameters (`Tree` uses
// `S::Unit`, `Forest` uses `U::Label`; the members' parameters are shared by position), at generic
// and at concrete uses.
pub trait Shape {
    type Unit;
    type Label;
}

pub enum Tree<S: Shape> {
    Leaf(S::Unit),
    Node(Forest<S>),
}

pub struct Forest<U: Shape> {
    pub trees: Vec<Tree<U>>,
    pub label: U::Label,
}

pub struct Square;

impl Shape for Square {
    type Unit = u32;
    type Label = bool;
}

pub fn leaves<S: Shape>(t: &Tree<S>) -> u32 {
    match t {
        Tree::Leaf(_) => 1,
        Tree::Node(f) => {
            let mut n = 0;
            for c in &f.trees {
                n += leaves(c);
            }
            n
        }
    }
}

pub fn square_leaf(x: u32) -> Tree<Square> {
    Tree::Leaf(x)
}

pub fn label_of(f: &Forest<Square>) -> bool {
    f.label
}

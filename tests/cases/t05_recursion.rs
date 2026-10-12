// Recursion (with fuel), mutual recursion, recursive data types.

pub fn fact(n: u64) -> u64 {
    if n == 0 { 1 } else { n * fact(n - 1) }
}

pub fn is_even(n: u32) -> bool {
    if n == 0 { true } else { is_odd(n - 1) }
}

pub fn is_odd(n: u32) -> bool {
    if n == 0 { false } else { is_even(n - 1) }
}

pub fn uses_fact(n: u64) -> u64 {
    fact(n) + 1
}

pub enum List {
    Nil,
    Cons(u32, Box<List>),
}

pub fn list_sum(l: &List) -> u32 {
    match l {
        List::Nil => 0,
        List::Cons(v, rest) => v + list_sum(rest),
    }
}

pub fn build(n: u32) -> List {
    if n == 0 { List::Nil } else { List::Cons(n, Box::new(build(n - 1))) }
}

pub struct Node {
    pub val: u32,
    pub next: Option<Box<Node>>,
}

pub fn node_len(n: &Node) -> u32 {
    match &n.next {
        None => 1,
        Some(m) => 1 + node_len(m),
    }
}

pub enum Expr {
    Lit(u32),
    Add(Box<Expr>, Box<Expr>),
    Neg(Box<Term>),
}

pub enum Term {
    Atom(u32),
    Wrap(Box<Expr>),
}

pub fn eval(e: &Expr) -> u32 {
    match e {
        Expr::Lit(v) => *v,
        Expr::Add(a, b) => eval(a) + eval(b),
        Expr::Neg(t) => eval_term(t),
    }
}

pub fn eval_term(t: &Term) -> u32 {
    match t {
        Term::Atom(v) => *v,
        Term::Wrap(e) => eval(e),
    }
}

pub fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

pub fn zero_arg_rec() -> u32 {
    if false { zero_arg_rec() } else { 3 }
}

// Dictionary fields whose types have associated types of the trait's other type parameters, as
// type parameters of a datatype: `Graph<L, N>` takes `L::Op` and `N::Data`, which the methods of
// `Analysis<L>` and `Searcher<L, N>` (bounded in their `where` clauses) take.
pub trait Language {
    type Op;
    fn op(&self) -> Self::Op;
}
pub trait Analysis<L: Language> {
    type Data;
    fn make(g: &Graph<L, Self>, n: &L) -> Self::Data
    where
        Self: Sized;
}
pub struct Graph<L: Language, N: Analysis<L>> {
    pub nodes: Vec<L>,
    pub ops: Vec<L::Op>,
    pub data: Vec<N::Data>,
}
pub trait Searcher<L: Language, N: Analysis<L>> {
    fn search(&self, g: &Graph<L, N>) -> usize;
}
pub fn make_first<L: Language, N: Analysis<L>>(g: &Graph<L, N>) -> Option<N::Data> {
    match g.nodes.first() {
        Some(n) => Some(N::make(g, n)),
        None => None,
    }
}
pub fn search_all<L: Language, N: Analysis<L>, S: Searcher<L, N>>(s: &S, g: &Graph<L, N>) -> usize {
    s.search(g)
}
pub struct Sym(pub u8);
impl Language for Sym {
    type Op = u8;
    fn op(&self) -> u8 { self.0 }
}
pub struct Count;
impl Analysis<Sym> for Count {
    type Data = u32;
    fn make(g: &Graph<Sym, Count>, _n: &Sym) -> u32 { g.ops.len() as u32 }
}
pub struct Len;
impl Searcher<Sym, Count> for Len {
    fn search(&self, g: &Graph<Sym, Count>) -> usize { g.nodes.len() + g.data.len() }
}
pub fn concrete(g: &Graph<Sym, Count>) -> usize { search_all(&Len, g) + make_first(g).map_or(0, |d| d as usize) }

// A dictionary that contains itself (as in jaq-core): the dictionary of `Data for J<V>` has, for
// the bound `Self::D: Has<Self>` of its associated type, the dictionary of `Has<J<V>> for
// L<J<V>>`, whose implementation requires `J<V>: Data`, the dictionary being built (generic code
// passes dictionaries; at concrete types functions are translated per instance). As a HOL term it
// would be infinite, so it is a placeholder instead of an endless recursion of the frontend.

use core::marker::PhantomData;

pub trait Data: 'static {
    type D: Has<Self>;
}

pub trait Has<T: Data + ?Sized> {
    fn get(&self) -> u32;
}

pub struct L<T>(pub PhantomData<T>, pub u32);

pub struct J<V>(pub PhantomData<V>);

impl<V: 'static> Data for J<V> {
    type D = L<J<V>>;
}

impl<T: Data> Has<T> for L<T> {
    fn get(&self) -> u32 {
        self.1
    }
}

pub fn use_data<X: Data>(d: &X::D) -> u32 {
    d.get()
}

pub fn run<V: 'static>(d: &L<J<V>>) -> u32 {
    use_data::<J<V>>(d)
}

pub fn plain(a: u32) -> u32 {
    a + 1
}

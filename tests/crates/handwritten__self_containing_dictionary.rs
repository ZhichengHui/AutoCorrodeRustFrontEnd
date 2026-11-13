// Dictionaries that contain themselves (as in jaq-core). The dictionary of `Data for J<V>` has,
// for the bound `Self::D: Has<Self>` of its associated type, the dictionary of `Has<J<V>> for
// L<J<V>>`, whose implementation requires `J<V>: Data`: the dictionary being built. In `G`, the
// same cycle needs the dictionary at a bigger argument each round (`G<V>` needs `G<Box<V>>`), which
// is cut at the nesting limit.
// Generic code passes dictionaries: as HOL terms they would be infinite, so its calls are
// placeholders instead of an endless recursion of the frontend. At concrete types the functions
// are translated per instance and need no dictionaries.

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

pub fn run_u8(d: &L<J<u8>>) -> u32 {
    use_data::<J<u8>>(d)
}

pub struct G<V>(pub PhantomData<V>);

pub struct M<T>(pub PhantomData<T>, pub u32);

impl<V: 'static> Data for G<V> {
    type D = M<G<V>>;
}

impl<V: 'static> Has<G<V>> for M<G<V>>
where
    G<Box<V>>: Data,
{
    fn get(&self) -> u32 {
        self.1
    }
}

pub fn run_growing<V: 'static>(d: &M<G<V>>) -> u32 {
    use_data::<G<V>>(d)
}

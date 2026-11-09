pub fn bump(const_at: &mut u32, mutable: &mut u32) {
    *const_at += 1;
    *mutable = *const_at;
}

pub fn mutate(x: &mut u32) -> &mut u32 {
    x
}

pub fn set_through_call(a: &mut u32) {
    *mutate(a) = 1;
}

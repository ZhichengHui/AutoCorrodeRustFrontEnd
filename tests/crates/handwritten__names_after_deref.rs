pub fn bump(const_at: &mut u32, mutable: &mut u32) {
    *const_at += 1;
    *mutable = *const_at;
}

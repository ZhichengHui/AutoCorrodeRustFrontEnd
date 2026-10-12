//@ charon-args=--consts=values

static mut FOO: &mut u32 = &mut 42;
static SHARED: &u32 = &42;

fn main() {
    unsafe {
        *FOO = 43;
    }
}

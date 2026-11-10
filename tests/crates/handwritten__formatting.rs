// `format!` and `write!` (with options and user `Display` impls), `Formatter` methods, function
// items as values, fieldless external enums and strings with special characters.
use core::fmt;

pub struct P { x: u32 }
impl fmt::Display for P {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "P({}, {:#x})", self.x, self.x + 1)?;
        if f.alternate() { f.write_str("!\n") } else { Ok(()) }
    }
}
pub fn show(p: &P) -> String { format!("[{:>6}|{p}|{:<4}|{:+}]", "ab", 7u8, -3i32) }
pub fn boxed(b: Box<u64>, w: usize) -> String { format!("{:0w$}{:?}", b, "q\"t") }
pub fn delegate(x: i16, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(&x, f) }
pub fn twice(x: u32) -> u32 { x * 2 }
pub fn map_twice(o: Option<u32>) -> Option<u32> { o.map(twice) }
pub fn same(a: u32, b: u32) -> u32 { assert_eq!(a, b); a }
pub fn line() -> &'static str { "a\tb\n" }

// Characters are code points: non-ASCII literals, ordering, ranges, casts, constants.
pub fn literals(c: char) -> bool { c == 'é' || c == '€' || c == '😀' || c == '\u{7f}' || c == '\'' }
pub fn ordering(a: char, b: char) -> bool { a < b || ('0' <= a && a <= '9') }
pub fn class(c: char) -> u32 {
    match c {
        '0'..='9' => 0,
        'a'..='z' | 'A'..='Z' => 1,
        'α'..='ω' => 2,
        '\u{10000}'.. => 3,
        _ => 4,
    }
}
pub fn casts(c: char, b: u8) -> (u32, u8, char, u64) { (c as u32, c as u8, b as char, u64::from(c)) }
pub fn from_byte(b: u8) -> char { char::from(b) }
pub fn limits() -> (char, char) { (char::MAX, char::REPLACEMENT_CHARACTER) }
pub fn max_of(a: char, b: char) -> core::cmp::Ordering { a.cmp(&b) }
pub fn sort_chars(v: &mut [char]) { v.sort() }
pub fn default_char() -> char { Default::default() }
pub const TABLE: [char; 3] = ['a', 'é', '😀'];
pub fn table(i: usize) -> char { TABLE[i] }

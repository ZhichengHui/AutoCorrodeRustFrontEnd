// UTF-8 validation, character conversions, the ASCII methods, parsing integers.
pub fn decode(b: &[u8]) -> Result<&str, core::str::Utf8Error> { core::str::from_utf8(b) }
pub fn decode_owned(v: Vec<u8>) -> Option<String> { String::from_utf8(v).ok() }
pub fn error_info(b: &[u8]) -> (usize, Option<usize>) {
    match core::str::from_utf8(b) {
        Ok(_) => (0, None),
        Err(e) => (e.valid_up_to(), e.error_len()),
    }
}
pub fn bytes_back(v: Vec<u8>) -> Vec<u8> {
    match String::from_utf8(v) {
        Ok(s) => s.into_bytes(),
        Err(e) => e.into_bytes(),
    }
}
pub fn unchecked(b: &[u8]) -> &str { unsafe { core::str::from_utf8_unchecked(b) } }
pub fn chars(n: u32, c: char) -> (Option<char>, Option<u32>, Option<char>, usize) {
    (char::from_u32(n), c.to_digit(16), char::from_digit(n, 10), c.len_utf8())
}
pub fn classes(c: char, b: u8) -> bool {
    c.is_whitespace() || c.is_control() || c.is_ascii_digit() || c.is_ascii_alphabetic()
        || b.is_ascii_hexdigit() || b.is_ascii_whitespace() || c.is_ascii()
}
pub fn upper(c: char, b: u8) -> (char, u8, bool) { (c.to_ascii_uppercase(), b.to_ascii_lowercase(), b.eq_ignore_ascii_case(&b'A')) }
pub fn parse(s: &str) -> (Result<u32, core::num::ParseIntError>, Result<i8, core::num::ParseIntError>) {
    (u32::from_str_radix(s, 16), i8::from_str_radix(s, 10))
}
pub fn parse_trait(s: &str) -> Option<u64> { s.parse::<u64>().ok() }
pub fn format(n: u32, c: char) -> String { format!("{}→{}{:>3}", n, c, 'é') }
pub fn describe(b: &[u8]) -> String {
    match core::str::from_utf8(b) {
        Ok(s) => format!("{:?}", s),
        Err(e) => format!("{} / {:?} / {:#?}", e, e, e),
    }
}

// `str` and `String` as UTF-8 bytes: building, measuring, slicing by byte ranges, searching.
pub fn build(c: char) -> String {
    let mut s = String::new();
    s.push_str("héllo");
    s.push(c);
    s.push('€');
    s += "!";
    s
}
pub fn lengths(s: &str, t: &String) -> (usize, usize, bool, bool) { (s.len(), t.len(), s.is_empty(), t.is_empty()) }
pub fn pop_and_truncate(s: &mut String) -> Option<char> { s.truncate(3); s.pop() }
pub fn slices(s: &str) -> (&str, &str, &str, &str, &str) { (&s[1..3], &s[..2], &s[2..], &s[..=1], &s[..]) }
pub fn get(s: &str) -> Option<&str> { s.get(0..2) }
pub fn split(s: &str) -> (&str, &str) { s.split_at(2) }
pub fn boundary(s: &str, i: usize) -> bool { s.is_char_boundary(i) }
pub fn patterns(s: &str) -> bool {
    s.starts_with('h') && s.starts_with("hé") && s.ends_with("!") && s.contains('€') && s.contains("ll")
}
pub fn strip(s: &str) -> (Option<&str>, Option<&str>) { (s.strip_prefix("é"), s.strip_suffix('x')) }
pub fn position(s: &str) -> Option<usize> { s.find('€') }
pub fn trims(s: &str) -> (&str, &str, &str) { (s.trim(), s.trim_start(), s.trim_end()) }
pub fn count_chars(s: &str) -> usize {
    let mut n = 0;
    for _c in s.chars() { n += 1; }
    n
}
pub fn last_index(s: &str) -> usize {
    let mut last = 0;
    for (i, _c) in s.char_indices() { last = i; }
    last
}
pub fn sum_bytes(s: &str) -> u32 {
    let mut n = 0u32;
    for b in s.bytes() { n += b as u32; }
    n
}
pub fn words(s: &str) -> usize {
    let mut n = 0;
    for _w in s.split_whitespace() { n += 1; }
    for _l in s.lines() { n += 1; }
    n
}
pub fn concat(a: String, b: &str) -> String { a + b }
pub fn repeat(s: &str) -> String { s.repeat(3) }
pub fn compare(a: &str, b: &str) -> core::cmp::Ordering { a.cmp(b) }
pub fn sort_strings(v: &mut [String]) { v.sort() }
pub fn char_string(c: char) -> (String, String) { (c.to_string(), String::from(c)) }
pub fn bytes_of(s: &str) -> &[u8] { s.as_bytes() }
pub fn into_bytes(s: String) -> Vec<u8> { s.into_bytes() }
pub fn ascii(s: &str, t: &str) -> (bool, bool, String) { (s.is_ascii(), s.eq_ignore_ascii_case(t), s.to_ascii_uppercase()) }

pub fn roundtrip(s: String) -> Option<String> {
    let b: Vec<u8> = s.into_bytes();
    String::from_utf8(b).ok()
}

pub fn f(a: Option<u32>, r: Result<u32, u8>, v: Vec<u8>) -> u64 { let x = a.unwrap() + r.unwrap(); let n = v.len() as u64; if a.is_some() && r.is_ok() { n + x as u64 } else { 0 } }

pub fn f(a: Result<u32, u8>) -> Result<u32, u8> { let x = a?; if x > 9 { return Err(1); } Ok(x) }

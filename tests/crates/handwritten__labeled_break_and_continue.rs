pub fn f(n: u32) -> u32 { let mut c = 0; 'o: for i in 0..n { for j in 0..n { if j > i { continue 'o; } if i + j > 10 { break 'o; } c += 1; } } c }

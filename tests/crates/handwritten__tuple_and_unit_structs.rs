pub struct M(pub u64); pub struct U; pub fn f(m: M) -> u64 { let M(v) = m; let _u = U; v + m.0 }

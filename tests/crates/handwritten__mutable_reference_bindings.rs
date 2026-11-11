// Bindings by mutable reference into `Some`, struct fields and tuple components (and into an enum variant, a placeholder).
pub struct S { pub a: u32, pub b: u32 }
pub enum E { A(u32), B }
pub fn bump(o: &mut Option<u32>) { if let Some(x) = o { *x += 1; } }
pub fn bump_local(mut o: Option<u32>) -> Option<u32> { if let Some(x) = &mut o { *x += 1; } o }
pub fn bump_match(o: &mut Option<u32>) -> u32 { match o { Some(x) => { *x += 1; *x } None => 0 } }
pub fn field(s: &mut S) { let S { a, .. } = s; *a += 1; }
pub fn explicit(mut s: S) -> u32 { let S { ref mut b, .. } = s; *b += 2; s.b }
pub fn tup(t: &mut (u32, u32)) { let (x, _) = t; *x = 5; }
pub fn variant(e: &mut E) { if let E::A(x) = e { *x += 1; } }

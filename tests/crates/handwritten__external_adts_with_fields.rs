// External ADTs declared with their constructors: generic enums, enums with external field types, a public tuple struct, and an associated type in a field (`Cow`).
use std::borrow::Cow;
use std::ops::Bound;
use std::num::Wrapping;
use std::net::{IpAddr, Ipv4Addr};
pub fn lo(b: Bound<u32>) -> u32 { match b { Bound::Included(x) => x, Bound::Excluded(x) => x + 1, Bound::Unbounded => 0 } }
pub fn mk(x: u32) -> Bound<u32> { Bound::Included(x) }
pub fn wr(x: u32) -> Wrapping<u32> { Wrapping(x) }
pub fn unwr(w: Wrapping<u32>) -> u32 { let Wrapping(x) = w; x }
pub fn cow(s: &[u8]) -> Cow<'_, [u8]> { Cow::Borrowed(s) }
pub fn cow_len(c: Cow<'_, [u8]>) -> usize { match c { Cow::Borrowed(b) => b.len(), Cow::Owned(v) => v.len() } }
pub fn ip(a: Ipv4Addr) -> IpAddr { IpAddr::V4(a) }
pub fn eq(a: u32, b: u32) -> u32 { assert_eq!(a, b); a }

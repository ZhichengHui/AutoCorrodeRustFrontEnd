// Models of standard library iterators (adapters, `next`, `count`, `collect`), `str` methods and
// integer parsing, `Option`/`Result` methods with closures, slice, `Vec` and integer methods,
// mutable borrows of subslices as call arguments and `for` iterables (copied in and written back),
// range values as `get` arguments, and functions with const generic parameters (per instance).

pub fn words(text: &str) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let toks: Vec<&str> = line.split_whitespace().collect();
        if let Some(first) = toks.first() {
            if first.starts_with('#') { continue; }
            out.push((i + 1, toks.len()));
        }
    }
    out
}

pub fn parse_all(toks: &[&str]) -> Result<Vec<u32>, usize> {
    let mut v = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        v.push(t.parse::<u32>().map_err(|_| i)?);
    }
    Ok(v)
}

pub fn signed(t: &str) -> Option<i8> { t.parse::<i8>().ok() }

pub fn common_prefix(a: &[u8], b: &[u8], skip: usize) -> usize {
    a.iter().zip(b).skip(skip).take_while(|(x, y)| x == y).count()
}

pub fn doubled(xs: &[u32]) -> Vec<u32> { xs.iter().map(|x| x * 2).collect() }

pub fn last_two(xs: &[u8]) -> Vec<u8> { xs.iter().rev().take(2).copied().collect() }

pub fn chunk_sums(xs: &[u8]) -> Vec<u32> {
    let mut out = Vec::new();
    for c in xs.chunks_exact(2) {
        out.push(u32::from(c[0]) + u32::from(c[1]));
    }
    out
}

pub fn lookup(xs: &[u16], i: usize) -> u16 { xs.get(i).copied().unwrap_or(0) }

pub fn head4(xs: &[u8]) -> Option<u32> {
    let h = xs.get(..4)?;
    let a: [u8; 4] = h.try_into().ok()?;
    Some(u32::from_le_bytes(a))
}

pub fn fill_mid(v: &mut Vec<u8>, a: usize, b: usize) {
    v[a..b].fill(7);
    zero(&mut v[..a]);
    for x in &mut v[b..] {
        *x += 1;
    }
}

fn zero(s: &mut [u8]) {
    for x in s.iter_mut() {
        *x = 0;
    }
}

pub fn edit(v: &mut Vec<u32>, n: usize) -> bool {
    v.truncate(n);
    v.extend_from_slice(&[1, 2]);
    v.resize(n + 3, 9);
    v.reverse();
    v.is_empty()
}

pub fn bits(x: u32, y: u64) -> u32 {
    x.wrapping_mul(3).wrapping_sub(1).trailing_zeros() + y.leading_zeros() + x.min(7) + core::cmp::max(x, 1)
}

pub fn opt(o: Option<u8>, r: Result<u8, u8>) -> Result<u16, u8> {
    let p = o.and_then(|x| x.checked_sub(1)).map(|x| u16::from(x)).ok_or_else(|| 3)?;
    r.map(|x| p + u16::from(x))
}

fn scaled<const K: u32, const ROUND: bool>(x: u32) -> u32 {
    if ROUND { (x + K - 1) / K * K } else { x * K }
}

pub fn scale_both(x: u32) -> u32 { scaled::<4, true>(x) + scaled::<2, false>(x) }

pub fn word_size() -> usize { core::mem::size_of::<u64>() }

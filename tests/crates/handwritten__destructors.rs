// Destructors: drops at the ends of scopes, early exits, moves (flags), assignments.

pub struct Log<'a> {
    out: &'a mut Vec<u8>,
    tag: u8,
}

impl Drop for Log<'_> {
    fn drop(&mut self) {
        self.out.push(self.tag);
    }
}

pub struct Pair<'a> {
    first: Log<'a>,
    n: u32,
}

fn consume(l: Log<'_>) -> u8 {
    l.tag
}

pub fn scopes(out: &mut Vec<u8>, early: bool) -> u32 {
    let a = Log { out, tag: 1 };
    if early {
        return 7;
    }
    let t = consume(a);
    u32::from(t)
}

pub fn checked(out: &mut Vec<u8>, x: Option<u8>) -> Option<u8> {
    let l = Log { out, tag: 2 };
    let v = x?;
    Some(v + l.tag)
}

pub fn looping(v: &mut Vec<u8>, n: u8) -> u8 {
    let mut i = 0;
    loop {
        let g = Log { out: &mut *v, tag: i };
        if i == n {
            break;
        }
        i += g.tag + 1;
    }
    i
}

pub fn reassign(v: &mut Vec<u8>) -> u32 {
    let mut p = Pair { first: Log { out: &mut *v, tag: 3 }, n: 1 };
    p.n += 1;
    let n = p.n;
    drop(p);
    n
}

pub fn temp(v: &mut Vec<u8>) {
    let _ = Log { out: v, tag: 4 };
}

pub fn boxed(b: Box<Log<'_>>) -> u8 {
    b.tag
}

pub fn matched(out: &mut Vec<u8>, x: Option<u8>) -> u8 {
    let l = Log { out, tag: 5 };
    match x {
        Some(v) => v + l.tag,
        None => return 0,
    }
}

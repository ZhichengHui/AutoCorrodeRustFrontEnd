pub struct Countdown {
    n: u32,
}

impl Iterator for Countdown {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.n == 0 {
            None
        } else {
            self.n -= 1;
            Some(self.n)
        }
    }
}

pub fn sum_countdown(n: u32, skip: u32, stop: u32) -> u32 {
    let mut s = 0;
    for x in (Countdown { n }) {
        if x == skip {
            continue;
        }
        if x == stop {
            break;
        }
        s += x;
    }
    s
}

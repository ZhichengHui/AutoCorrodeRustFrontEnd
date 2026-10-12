// A small byte tokenizer and a state machine, written as ordinary library code.

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Token {
    Num(u32),
    Plus,
    Minus,
    Star,
    LParen,
    RParen,
    End,
    Bad(u8),
}

pub struct Lexer {
    pub input: Vec<u8>,
    pub pos: usize,
}

impl Lexer {
    pub fn new(input: Vec<u8>) -> Lexer {
        Lexer { input, pos: 0 }
    }

    fn peek(&self) -> Option<u8> {
        if self.pos < self.input.len() { Some(self.input[self.pos]) } else { None }
    }

    fn skip_spaces(&mut self) {
        while let Some(b) = self.peek() {
            if b != b' ' {
                break;
            }
            self.pos += 1;
        }
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_spaces();
        let Some(b) = self.peek() else {
            return Token::End;
        };
        self.pos += 1;
        match b {
            b'+' => Token::Plus,
            b'-' => Token::Minus,
            b'*' => Token::Star,
            b'(' => Token::LParen,
            b')' => Token::RParen,
            b'0'..=b'9' => {
                let mut v = (b - b'0') as u32;
                while let Some(d) = self.peek() {
                    if d < b'0' || d > b'9' {
                        break;
                    }
                    v = v * 10 + (d - b'0') as u32;
                    self.pos += 1;
                }
                Token::Num(v)
            }
            other => Token::Bad(other),
        }
    }
}

pub fn count_tokens(input: Vec<u8>) -> u32 {
    let mut lx = Lexer::new(input);
    let mut n = 0;
    loop {
        let t = lx.next_token();
        if t == Token::End {
            break;
        }
        n += 1;
    }
    n
}

#[derive(Clone, Copy, PartialEq)]
pub enum State {
    Idle,
    Running { ticks: u32 },
    Done(u32),
}

pub fn step(s: State, go: bool) -> State {
    match s {
        State::Idle if go => State::Running { ticks: 0 },
        State::Idle => State::Idle,
        State::Running { ticks } if ticks >= 3 => State::Done(ticks),
        State::Running { ticks } => State::Running { ticks: ticks + 1 },
        State::Done(t) => State::Done(t),
    }
}

pub fn run_machine(n: u32) -> u32 {
    let mut s = State::Idle;
    for i in 0..n {
        s = step(s, i > 0);
    }
    match s {
        State::Done(t) => t,
        _ => 0,
    }
}

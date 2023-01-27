use std::time::{Duration, Instant};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Timings {
    pub lex: Duration,
    pub parse: Duration,
    pub resolve: Duration,
    pub interpret: Duration,
}

impl Timings {
    pub fn new(lex: Duration, parse: Duration, resolve: Duration, interpret: Duration) -> Self {
        Self {
            lex,
            parse,
            resolve,
            interpret,
        }
    }

    pub fn total(&self) -> Duration {
        self.lex + self.parse + self.resolve + self.interpret
    }
}

pub struct TimingsBuilder {
    timings: Timings,
}

impl TimingsBuilder {
    pub fn new() -> Self {
        Self {
            timings: Timings {
                lex: Duration::default(),
                parse: Duration::default(),
                resolve: Duration::default(),
                interpret: Duration::default(),
            },
        }
    }

    pub fn lex<T>(&mut self, f: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let result = f();
        self.timings.lex = start.elapsed();
        result
    }

    pub fn parse<T>(&mut self, f: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let result = f();
        self.timings.parse = start.elapsed();
        result
    }

    pub fn resolve<T>(&mut self, f: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let result = f();
        self.timings.resolve = start.elapsed();
        result
    }

    pub(crate) fn interpret<T>(&mut self, f: impl FnOnce() -> T) -> T {
        let start = Instant::now();
        let result = f();
        self.timings.interpret = start.elapsed();
        result
    }

    pub fn build(self) -> Timings {
        self.timings
    }
}

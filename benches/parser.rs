#![cfg(benches)]
#![feature(test)]

extern crate test;
use std::vec::Vec;

use test::Bencher;

#[bench]
fn crox_parser(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    let source = crox::scan(input);
    let tokens = source.scan_all().unwrap();
    b.bytes = input.len() as u64;
    b.iter(|| crox::stmt_parser(source, tokens.iter().copied()).collect::<Vec<_>>());
}

#[bench]
fn crox_scanner_then_parser(b: &mut Bencher) {
    let input = include_str!("../tests/classes.crox");
    let source = crox::scan(input);
    b.bytes = input.len() as u64;
    b.iter(|| {
        crox::stmt_parser(source, source.into_iter().map(Result::unwrap)).collect::<Vec<_>>()
    });
}

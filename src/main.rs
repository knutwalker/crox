use std::{
    fs,
    io::{self, Write},
    path::Path,
};

use crox::{Ast, CroxErrors, ValueExpr};

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", e);
    }
}

fn run() -> io::Result<()> {
    let mut args = std::env::args_os().skip(1);
    let file = args.next();

    if args.next().is_some() {
        println!("Usage: crox [script]");
        std::process::exit(64);
    }

    match file {
        Some(file) => match run_file(file)? {
            Ok(_) => {}
            Err(e) => {
                report_error(e);
                std::process::exit(65)
            }
        },
        None => repl()?,
    }

    Ok(())
}

fn run_file(file: impl AsRef<Path>) -> io::Result<crox::Result> {
    let content = fs::read_to_string(file)?;
    let res = crox::run(&content).map(|exprs| report_ok(false, exprs));
    Ok(res)
}

fn repl() -> io::Result<()> {
    let verbose = std::env::var_os("CROX_VERBOSE").is_some();

    let mut line = String::new();

    loop {
        print!("> ");
        io::stdout().flush()?;

        line.clear();
        io::stdin().read_line(&mut line)?;

        let line = line.trim();

        if line.is_empty() {
            break;
        }

        handle(verbose, line.trim());
    }

    Ok(())
}

fn handle(verbose: bool, line: &str) {
    match crox::run(line) {
        Ok(res) => report_ok(verbose, res),
        Err(e) => report_error(e),
    }
}

fn report_ok(verbose: bool, (exprs, ast): (Vec<ValueExpr>, Ast)) {
    for value in exprs {
        if verbose {
            let expr = value.expr.resolve(&ast);
            println!("{:#?}", expr);
            println!("{:#?}", value);
        }
        println!("{}", value.value);
    }
}

#[cfg(feature = "fancy")]
fn report_error(err: CroxErrors) {
    let err = miette::Report::new(err);
    eprintln!("{:?}", err);
}

#[cfg(not(feature = "fancy"))]
fn report_error(err: CroxErrors) {
    eprintln!("{:#}", err);
}

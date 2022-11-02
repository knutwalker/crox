use std::{
    fs,
    io::{self, Write},
    path::Path,
};

use crox::{Ast, CroxErrors, Expr};

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
    let res = crox::run(&content).map(report_ok);
    Ok(res)
}

fn repl() -> io::Result<()> {
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

        handle(line);
    }

    Ok(())
}

fn handle(line: &str) {
    match crox::run(line) {
        Ok(res) => report_ok(res),
        Err(e) => report_error(e),
    }
}

fn report_ok((exprs, ast): (Vec<Expr>, Ast)) {
    for expr in exprs {
        let expr = expr.resolve(&ast);
        println!("{:#?}", expr);
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

use std::{
    fs,
    io::{self, Write},
    path::Path,
};

use crox::{CroxErrors, Node, ScanError};

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
    Ok(crox::run(&content))
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
    let mut errs = Vec::new();

    let source = crox::scan(line);

    let tokens = source.into_iter().filter_map(|t| match t {
        Ok(t) => Some(t),
        Err(e) => {
            errs.push(e);
            None
        }
    });

    let expr = crox::parser(tokens);
    let expr = match expr {
        Ok(expr) => expr,
        Err((msg, span)) => {
            errs.push(ScanError {
                kind: crox::ScanErrorKind::Other(msg),
                span: span.into(),
            });
            Node::nil().into_expr(0..0)
        }
    };

    if errs.is_empty() {
        println!("{:#?}", expr);
    } else {
        report_error(CroxErrors::from((source.source, errs)))
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

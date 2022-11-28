use crox::{Ast, CroxError, CroxErrorKind, CroxErrorScope, CroxErrors, Node, TokenType, Value};
use std::{
    fmt::Debug,
    fs::{self, File},
    io::{self, Read, Seek, Write},
    path::Path,
};

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

    let res = match open_script(file)? {
        Some(content) if !content.trim().is_empty() => run_script(&content),
        _ => Ok(repl()?),
    };

    if let Err(e) = res {
        let scope = e.scope();
        report_error(e);
        let exit_code = match scope {
            CroxErrorScope::Custom | CroxErrorScope::Scanner | CroxErrorScope::Parser => 65,
            CroxErrorScope::Interpreter => 70,
        };
        std::process::exit(exit_code)
    }

    Ok(())
}

fn open_script(file: Option<impl AsRef<Path>>) -> io::Result<Option<String>> {
    match file {
        Some(file) => fs::read_to_string(file).map(Some),
        None => {
            let stdin = io::stdin();

            #[cfg(unix)]
            let file = {
                use std::os::unix::prelude::AsFd;
                let stdin = stdin.as_fd().try_clone_to_owned();
                stdin.map(File::from)
            };

            #[cfg(windows)]
            let file = {
                use std::os::windows::io::AsHandle;
                let stdin = std.as_handle().try_clone_to_owned();
                stdin.map(File::from)
            };

            #[cfg(not(any(unix, windows)))]
            compile_error!("Unsupported platform, only unix and windows are supported");

            let has_stdin = file.map_or(false, |mut f| {
                f.seek(io::SeekFrom::End(0)).map_or(true, |len| len > 0)
            });

            Ok(if has_stdin {
                let mut content = String::new();
                io::stdin().read_to_string(&mut content)?;
                Some(content)
            } else {
                None
            })
        }
    }
}

fn run_script(content: &str) -> crox::Result<(), CroxErrors> {
    crox::run(content).map(|exprs| report_ok(false, exprs))
}

fn repl() -> io::Result<()> {
    let verbose = std::env::var_os("CROX_VERBOSE").is_some();

    let mut line = String::new();

    loop {
        print!("> ");
        io::stdout().flush()?;

        line.clear();
        io::stdin().read_line(&mut line)?;

        if line.is_empty() {
            break;
        }

        handle(verbose, line.trim());
    }

    Ok(())
}

fn handle(verbose: bool, line: &str) {
    fn is_semicolon_instead_of_eof(error: &CroxError, line: &str) -> bool {
        if error.span == (0..line.len()) {
            if let CroxErrorKind::UnexpectedEndOfInput {
                expected: Some(expected),
            } = &error.kind
            {
                if expected.len() == 1 && expected.contains(TokenType::Semicolon) {
                    return true;
                }
            }
        }

        false
    }

    match crox::run(line) {
        Ok(res) => report_ok(verbose, res),
        Err(e) => match e.errors() {
            [e] if is_semicolon_instead_of_eof(e, line) => match crox::eval(line) {
                Ok(res) => report_ok(verbose, res),
                Err(e) => report_error(e),
            },
            _ => report_error(e),
        },
    }
}

fn report_ok<T: Debug>(verbose: bool, ast: Ast<Node<T>>) {
    for node in ast.iter() {
        let value = &node.value;
        if verbose {
            println!("{:#?}", node.item);
            println!("{:#?}", value);
        }
        if value != &Value::Nil {
            println!("{}", value);
        }
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

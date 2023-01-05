use crox::{CroxError, CroxErrorKind, CroxErrors, TokenType};
use std::{
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
        std::process::exit(e)
    }

    Ok(())
}

fn open_script(file: Option<impl AsRef<Path>>) -> io::Result<Option<String>> {
    match file {
        Some(file) => fs::read_to_string(file).map(Some),
        None => {
            #[cfg(unix)]
            let stdio_file = {
                use std::os::unix::prelude::AsFd;
                let stdin = io::stdin();
                let stdin = stdin.as_fd().try_clone_to_owned();
                stdin.map(File::from).ok()
            };

            #[cfg(windows)]
            let stdio_file = {
                use std::os::windows::io::AsHandle;
                let stdin = io::stdin();
                let stdin = std.as_handle().try_clone_to_owned();
                stdin.map(File::from).ok()
            };

            #[cfg(not(any(unix, windows)))]
            let std_file = None;

            let has_stdin = stdio_file.map_or(false, |mut f| {
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

fn run_script(content: &str) -> crox::Result<(), i32> {
    let ast = crox::run_as_script(true, std::io::stdout(), std::io::stderr(), content)?;
    crox::print_ast(false, ast);
    Ok(())
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

    match crox::run(std::io::stdout(), line) {
        Ok(res) => crox::print_ast(verbose, res),
        Err(e) => match e.errors() {
            [e] if is_semicolon_instead_of_eof(e, line) => {
                match crox::eval(std::io::stdout(), line) {
                    Ok(res) => crox::print_ast(verbose, res),
                    Err(e) => report_error(e),
                }
            }
            _ => report_error(e),
        },
    }
}

fn report_error(err: CroxErrors) {
    let stderr = std::io::stderr().lock();
    crox::report_error(true, stderr, err);
}

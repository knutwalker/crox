#![warn(clippy::all, clippy::nursery)]
#![warn(clippy::pedantic)]
#![warn(
    bad_style,
    dead_code,
    improper_ctypes,
    missing_copy_implementations,
    missing_debug_implementations,
    // missing_docs,
    no_mangle_generic_items,
    non_shorthand_field_patterns,
    overflowing_literals,
    path_statements,
    patterns_in_fns_without_body,
    private_in_public,
    rust_2018_idioms,
    trivial_casts,
    trivial_numeric_casts,
    unconditional_recursion,
    unsafe_op_in_unsafe_fn,
    unused_allocation,
    unused_comparisons,
    unused_extern_crates,
    unused_import_braces,
    unused_parens,
    unused_qualifications,
    unused_results,
    unused,
    while_true
)]

mod frontend;
mod repl;

use std::{
    fs::{self, File},
    io::{self, Read, Seek},
    path::Path,
};

use bumpalo::Bump;

fn main() {
    let ec = match run() {
        Ok(ec) => ec,
        Err(e) => {
            eprintln!("{e}");
            1
        }
    };
    std::process::exit(ec);
}

fn run() -> io::Result<i32> {
    let mut args = std::env::args_os().skip(1);
    let file = args.next();

    if args.next().is_some() {
        println!("Usage: crox [script]");
        return Ok(64);
    }

    let res = match open_script(file)? {
        Some(content) if !content.trim().is_empty() => run_script(&content),
        _ => Ok(repl()?),
    };

    if let Err(e) = res {
        return Ok(e);
    }

    Ok(0)
}

fn open_script(file: Option<impl AsRef<Path>>) -> io::Result<Option<String>> {
    if let Some(file) = file {
        fs::read_to_string(file).map(Some)
    } else {
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
            let _ = io::stdin().read_to_string(&mut content)?;
            Some(content)
        } else {
            None
        })
    }
}

fn run_script(content: &str) -> crox::Result<(), i32> {
    let arena = Bump::new();
    let ast = crox::run_as_script(true, std::io::stdout(), std::io::stderr(), &arena, content)?;
    crox::print_ast(std::io::stdout(), None, &ast);
    Ok(())
}

fn repl() -> io::Result<()> {
    repl::Repl::run()
}

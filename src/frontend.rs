use std::io::Write;

use bumpalo::Bump;
use crox::{Config, CroxError, CroxErrorKind, CroxErrors, Environment, TokenType};

pub struct Frontend {
    env: Environment<'static>,
    arena: &'static Bump,
}

impl Frontend {
    pub fn new() -> Self {
        let arena = Bump::new();
        let arena = Box::new(arena);
        let arena = Box::leak(arena);
        let env = Environment::default();
        Self { env, arena }
    }

    pub fn run(&self, mut out: impl Write, err: impl Write, line: &str, config: Option<Config>) {
        fn is_semicolon_instead_of_eof(error: &CroxError) -> bool {
            if let CroxErrorKind::UnexpectedEndOfInput {
                expected: Some(expected),
            } = &error.kind
            {
                if expected.len() == 1 && expected.contains(TokenType::Semicolon) {
                    return true;
                }
            }

            false
        }

        let line = self.arena.alloc_str(line.trim_end());

        match crox::run_with_env(&mut out, self.env.clone(), line) {
            Ok(res) => crox::print_ast(out, config, res),
            Err(e) => match e.errors() {
                [e] if is_semicolon_instead_of_eof(e) => {
                    match crox::eval_with_env(&mut out, self.env.clone(), line) {
                        Ok(res) => crox::print_ast(out, config, res),
                        Err(e) => report_error(err, e),
                    }
                }
                _ => report_error(err, e),
            },
        }
    }

    pub fn print_vars(&self, out: impl Write) {
        self.env.print_vars(out);
    }
}

fn report_error(err: impl Write, errors: CroxErrors) {
    let fancy = !cfg!(test);
    crox::report_error(fancy, err, errors);
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_handle_fallback_to_expr() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        Frontend::new().run(&mut out, &mut err, "1 + 2", None);

        assert_eq!(String::from_utf8(out).unwrap(), "3\n");
        assert_eq!(String::from_utf8(err).unwrap(), "");
    }

    #[test]
    fn test_handle_fallback_to_expr_if_other_errors() {
        let mut out = Vec::new();
        let mut err = Vec::new();
        Frontend::new().run(&mut out, &mut err, r#"1 < "2""#, None);

        assert_eq!(String::from_utf8(out).unwrap(), "");
        assert_eq!(
            String::from_utf8(err).unwrap(),
            r#"[line 1, offset 5] Error: Invalid type: expected [Number], got 'String'
1 < "2"
~~~~~^

"#
        );
    }
}

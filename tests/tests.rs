use crox::{scan, CroxErrors, Result, Token, TokenType};
use TokenType::*;

fn run_test(content: &str, expected: Vec<Token>) -> Result<(), CroxErrors> {
    use pretty_assertions::assert_eq;

    let source = scan(content);
    let actual = source.scan_all()?;

    assert_eq!(actual, expected);

    #[cfg(feature = "chumsky")]
    {
        let actual = source.scan_chumsky()?;
        assert_eq!(actual, expected);
    }

    #[cfg(feature = "nom")]
    {
        let actual = source.scan_nom()?;
        assert_eq!(actual, expected);
    }

    Ok(())
}

#[test]
fn test_classes() -> Result<(), CroxErrors> {
    run_test(include_str!("classes.crox"), include!("classes.tokens"))
}

#[test]
fn test_control_flow() -> Result<(), CroxErrors> {
    run_test(
        include_str!("control_flow.crox"),
        include!("control_flow.tokens"),
    )
}

#[test]
fn test_expressions() -> Result<(), CroxErrors> {
    run_test(
        include_str!("expressions.crox"),
        include!("expressions.tokens"),
    )
}

#[test]
fn test_functions() -> Result<(), CroxErrors> {
    run_test(include_str!("functions.crox"), include!("functions.tokens"))
}

#[test]
fn test_hello_world() -> Result<(), CroxErrors> {
    run_test(
        include_str!("hello_world.crox"),
        include!("hello_world.tokens"),
    )
}

#[test]
fn test_statements() -> Result<(), CroxErrors> {
    run_test(
        include_str!("statements.crox"),
        include!("statements.tokens"),
    )
}

#[test]
fn test_types() -> Result<(), CroxErrors> {
    run_test(include_str!("types.crox"), include!("types.tokens"))
}

#[test]
fn test_variables() -> Result<(), CroxErrors> {
    run_test(include_str!("variables.crox"), include!("variables.tokens"))
}

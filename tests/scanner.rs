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
    run_test(
        include_str!("scanner/classes.crox"),
        include!("scanner/classes.tokens"),
    )
}

#[test]
fn test_control_flow() -> Result<(), CroxErrors> {
    run_test(
        include_str!("scanner/control_flow.crox"),
        include!("scanner/control_flow.tokens"),
    )
}

#[test]
fn test_expressions() -> Result<(), CroxErrors> {
    run_test(
        include_str!("scanner/expressions.crox"),
        include!("scanner/expressions.tokens"),
    )
}

#[test]
fn test_functions() -> Result<(), CroxErrors> {
    run_test(
        include_str!("scanner/functions.crox"),
        include!("scanner/functions.tokens"),
    )
}

#[test]
fn test_hello_world() -> Result<(), CroxErrors> {
    run_test(
        include_str!("scanner/hello_world.crox"),
        include!("scanner/hello_world.tokens"),
    )
}

#[test]
fn test_statements() -> Result<(), CroxErrors> {
    run_test(
        include_str!("scanner/statements.crox"),
        include!("scanner/statements.tokens"),
    )
}

#[test]
fn test_types() -> Result<(), CroxErrors> {
    run_test(
        include_str!("scanner/types.crox"),
        include!("scanner/types.tokens"),
    )
}

#[test]
fn test_variables() -> Result<(), CroxErrors> {
    run_test(
        include_str!("scanner/variables.crox"),
        include!("scanner/variables.tokens"),
    )
}

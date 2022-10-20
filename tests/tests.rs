use crox::{scan, Result, Token, TokenType};
use TokenType::*;

fn run_test(content: &str, expected: Vec<Token>) -> Result {
    use pretty_assertions::assert_eq;

    let source = scan(content);
    let actual = source.into_iter().collect::<Result<Vec<_>>>()?;
    assert_eq!(actual, expected);

    #[cfg(feature = "chumsky")]
    {
        let actual = source.into_chumsky()?;
        assert_eq!(actual, expected);
    }

    #[cfg(feature = "nom")]
    {
        let actual = source.into_nom()?;
        assert_eq!(actual, expected);
    }

    Ok(())
}

#[test]
fn test_classes() -> Result {
    run_test(include_str!("classes.crox"), include!("classes.tokens"))
}

#[test]
fn test_control_flow() -> Result {
    run_test(
        include_str!("control_flow.crox"),
        include!("control_flow.tokens"),
    )
}

#[test]
fn test_expressions() -> Result {
    run_test(
        include_str!("expressions.crox"),
        include!("expressions.tokens"),
    )
}

#[test]
fn test_functions() -> Result {
    run_test(include_str!("functions.crox"), include!("functions.tokens"))
}

#[test]
fn test_hello_world() -> Result {
    run_test(
        include_str!("hello_world.crox"),
        include!("hello_world.tokens"),
    )
}

#[test]
fn test_statements() -> Result {
    run_test(
        include_str!("statements.crox"),
        include!("statements.tokens"),
    )
}

#[test]
fn test_types() -> Result {
    run_test(include_str!("types.crox"), include!("types.tokens"))
}

#[test]
fn test_variables() -> Result {
    run_test(include_str!("variables.crox"), include!("variables.tokens"))
}

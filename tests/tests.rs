#[test]
fn test_classes() -> crox::Result {
    crox::run(include_str!("classes.crox"))
}

#[test]
fn test_control_flow() -> crox::Result {
    crox::run(include_str!("control_flow.crox"))
}

#[test]
fn test_expressions() -> crox::Result {
    crox::run(include_str!("expressions.crox"))
}

#[test]
fn test_functions() -> crox::Result {
    crox::run(include_str!("functions.crox"))
}

#[test]
fn test_hello_world() -> crox::Result {
    crox::run(include_str!("hello_world.crox"))
}

#[test]
fn test_statements() -> crox::Result {
    crox::run(include_str!("statements.crox"))
}

#[test]
fn test_types() -> crox::Result {
    crox::run(include_str!("types.crox"))
}

#[test]
fn test_variables() -> crox::Result {
    crox::run(include_str!("variables.crox"))
}

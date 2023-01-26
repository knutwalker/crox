use once_cell::sync::Lazy;

use crate::suites::{AllSuites, Run};

mod suites;

static ALL_SUITES: Lazy<AllSuites> = Lazy::new(AllSuites::define);

#[test]
fn test_chapter4() {
    ALL_SUITES.run(Run::Chapter4Scanning);
}

#[test]
fn test_chapter6() {
    ALL_SUITES.run(Run::Chapter6Parsing);
}

#[test]
fn test_chapter7() {
    ALL_SUITES.run(Run::Chapter7Evaluating);
}

#[test]
fn test_chapter8() {
    ALL_SUITES.run(Run::Chapter8Statements);
}

#[test]
fn test_chapter9() {
    ALL_SUITES.run(Run::Chapter9Control);
}

#[test]
fn test_chapter10() {
    ALL_SUITES.run(Run::Chapter10Functions);
}

#[test]
fn test_chapter11() {
    ALL_SUITES.run(Run::Chapter11Resolving);
}

#[test]
fn test_chapter12() {
    ALL_SUITES.run(Run::Chapter12Classes);
}

#[test]
fn test_chapter13() {
    ALL_SUITES.run(Run::Chapter13Inheritance);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter17() {
    ALL_SUITES.run(Run::Chapter17Compiling);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter18() {
    ALL_SUITES.run(Run::Chapter18Types);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter19() {
    ALL_SUITES.run(Run::Chapter19Strings);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter20() {
    ALL_SUITES.run(Run::Chapter20Hash);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter21() {
    ALL_SUITES.run(Run::Chapter21Global);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter22() {
    ALL_SUITES.run(Run::Chapter22Local);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter23() {
    ALL_SUITES.run(Run::Chapter23Jumping);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter24() {
    ALL_SUITES.run(Run::Chapter24Calls);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter25() {
    ALL_SUITES.run(Run::Chapter25Closures);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter26() {
    ALL_SUITES.run(Run::Chapter26Garbage);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter27() {
    ALL_SUITES.run(Run::Chapter27Classes);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter28() {
    ALL_SUITES.run(Run::Chapter28Methods);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter29() {
    ALL_SUITES.run(Run::Chapter29Superclasses);
}

#[test]
#[ignore = "not yet implemented"]
fn test_chapter30() {
    ALL_SUITES.run(Run::Chapter30Optimization);
}

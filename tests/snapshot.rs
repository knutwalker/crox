use std::path::PathBuf;

use suites::Suite;
use walkdir::WalkDir;

use crate::suites::{AllSuites, Test, TestResult};

mod suites;

#[test]
fn test_implementation() {
    let suites = AllSuites::define();
    let suites = suites.get("chap08_statements");
    run_suites(suites);
}

fn run_suites<'a>(suites: impl IntoIterator<Item = &'a Suite>) {
    let all_successful = suites
        .into_iter()
        .inspect(|s| println!("=== {} ===", s.name))
        .map(run_suite)
        .reduce(|a, b| a && b)
        .unwrap_or(true);

    if !all_successful {
        std::process::exit(1)
    }
}

fn run_suite(suite: &Suite) -> bool {
    let mut result = SuiteResult::default();

    let walker = WalkDir::new("tests").into_iter();
    let walker = walker
        .filter_entry(|e| {
            e.file_type().is_dir() || e.path().extension().and_then(|e| e.to_str()) == Some("lox")
        })
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file());
    for entry in walker {
        run_test(entry.path().to_path_buf(), suite, &mut result);
    }

    if result.failed == 0 {
        println!(
            "All {} tests passed ({} expectations).",
            result.passed, result.expectations
        );
        true
    } else {
        println!(
            "{} test passed. {} tests failed.",
            result.passed, result.failed
        );
        false
    }
}

fn run_test(path: PathBuf, suite: &Suite, result: &mut SuiteResult) {
    if path.iter().any(|p| p == "benchmark") {
        return;
    }

    // filter subtest

    let test = Test::parse(path, suite);
    let test = match test {
        Ok(test) => {
            result.expectations += test.expectations();
            test
        }
        Err(e) => {
            match e {
                TestResult::Unknown(p) => panic!("Unknown test for {}", p.display()),
                TestResult::Missing(p) => panic!("No test file for {}", p.display()),
                TestResult::MixedErrorAssertions(p, (a, b)) => panic!(
                    "Test {} has mixed error assertions with exit codes {} and {}",
                    p.display(),
                    a,
                    b
                ),
                TestResult::Skipped => {
                    result.skipped += 1;
                }
                TestResult::NotATest => {}
            };
            return;
        }
    };

    println!("Testing {}", test.path().display());

    let failures = test.run();
    if failures.is_empty() {
        result.passed += 1;
    } else {
        result.failed += 1;
        eprintln!("FAIL: {}", test.path().display());
        for failure in failures {
            eprintln!("     {}", failure);
        }
    }

    println!(
        "Passed: {} Failed: {} Skipped: {}",
        result.passed, result.failed, result.skipped
    )
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
struct SuiteResult {
    passed: usize,
    failed: usize,
    skipped: usize,
    expectations: usize,
}

use std::{
    collections::HashSet,
    io::Write,
    path::{Path, PathBuf},
};

use crate::suites::{LangLevel, State, Suite, SuiteResult};

use once_cell::sync::Lazy;
use regex::Regex;

macro_rules! re {
    ($s:literal) => {
        ::once_cell::sync::Lazy::new(|| ::regex::Regex::new($s).unwrap())
    };
}

static EXPECTED_OUTPUT: Lazy<Regex> = re!(r#"// expect: ?(.*)"#);
static EXPECTED_ERROR: Lazy<Regex> = re!(r#"// (Error.*)"#);
static ERROR_LINE: Lazy<Regex> =
    re!(r#"// \[(?:(java|c) )?(?:line (\d+), )?offset (\d+)\](?: Error:)? (.*)"#);
static EXPECTED_RUNTIME_ERROR: Lazy<Regex> = re!(r#"// expect runtime error: (.+)"#);
static _CARET: Lazy<Regex> = re!(r#"// caret: (.+)"#);
static SYNTAX_ERROR: Lazy<Regex> = re!(r#"\[.*line (\d+), offset (\d+)\] Error: (.+)"#);
static _STACK_TRACE: Lazy<Regex> = re!(r#"\[line (\d+)\]"#);
static NON_TEST: Lazy<Regex> = re!(r#"// nontest"#);

pub struct Test {
    path: PathBuf,
    content: String,
    expected_outputs: Vec<ExpectedOutput>,
    expected_errors: HashSet<ExpectedError>,
}

impl Test {
    pub(super) fn run_from(path: PathBuf, suite: &Suite, result: &mut SuiteResult) {
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

        print!("Testing {}{:>20}\r", test.path().display(), " ");
        std::io::stdout().flush().unwrap();

        let failures = test.run(suite.lang);
        if failures.is_empty() {
            result.passed += 1;
        } else {
            result.failed += 1;
            eprintln!("\nFAIL: {}", test.path().display());
            for failure in failures {
                eprintln!("     {}", failure);
            }
        }

        print!(
            "Passed: {} Failed: {} Skipped: {}{:>20}\r",
            result.passed, result.failed, result.skipped, " "
        );
        std::io::stdout().flush().unwrap();
    }

    fn parse(path: PathBuf, suite: &Suite) -> Result<Test, TestResult> {
        let state = path
            .ancestors()
            .filter_map(|p| p.to_str())
            .find_map(|p| suite.tests.get(&p));

        match state {
            None => return Err(TestResult::Unknown(path)),
            Some(State::Skip) => return Err(TestResult::Skipped),
            Some(State::Pass) => {}
        };

        let content = match std::fs::read_to_string(&path) {
            Ok(f) => f,
            Err(_) => return Err(TestResult::Missing(path)),
        };

        let mut expected_outputs = Vec::new();
        let mut expected_errors = HashSet::new();

        for (line_no, line) in content
            .lines()
            .enumerate()
            .map(|(line_no, line)| (line_no + 1, line))
            .peekable()
        {
            match Self::parse_line(line, line_no, suite.lang) {
                Some(Ok(Ok(output))) => {
                    expected_outputs.push(output);
                }
                Some(Ok(Err(error))) => {
                    expected_errors.insert(error);
                }
                Some(Err(e)) => return Err(e),
                None => {}
            }
        }

        let exit_codes = expected_errors
            .iter()
            .map(|e| e.exit_code)
            .try_fold(None, |a, b| match (a, b) {
                (None, b) => Ok(Some(b)),
                (Some(a), b) if a == b => Ok(Some(b)),
                (Some(a), b) => Err((a, b)),
            });

        if let Err(mixed) = exit_codes {
            return Err(TestResult::MixedErrorAssertions(path, mixed));
        }

        Ok(Self {
            path,
            content,
            expected_outputs,
            expected_errors,
        })
    }

    fn parse_line(
        line: &str,
        line_no: usize,
        lang: LangLevel,
    ) -> Option<Result<Result<ExpectedOutput, ExpectedError>, TestResult>> {
        if NON_TEST.is_match(line) {
            return Some(Err(TestResult::NotATest));
        }

        if let Some(output) = EXPECTED_OUTPUT.captures(line) {
            return Some(Ok(Ok(ExpectedOutput::new(line_no, output[1].to_owned()))));
        }

        if let Some(error) = ERROR_LINE.captures(line) {
            if error.get(1).map_or(true, |l| lang == *l.as_str()) {
                return Some(Ok(Err(ExpectedError::new(
                    error[4].to_owned(),
                    error
                        .get(2)
                        .map_or(line_no, |l| l.as_str().parse().unwrap()),
                    error[3].parse().unwrap(),
                    65,
                ))));
            }
        }

        if let Some(error) = EXPECTED_ERROR.captures(line) {
            return Some(Ok(Err(ExpectedError::new(
                error[1].to_owned(),
                line_no,
                usize::MAX - 1,
                65,
            ))));
        }

        if let Some(error) = EXPECTED_RUNTIME_ERROR.captures(line) {
            return Some(Ok(Err(ExpectedError::new(
                error[1].to_owned(),
                line_no,
                usize::MAX - 1,
                70,
            ))));
        }

        None
    }

    pub fn expectations(&self) -> usize {
        self.expected_outputs.len() + self.expected_errors.len()
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn run(&self, lang: LangLevel) -> Vec<String> {
        let (stdout, stderr) = self.run_script(lang);

        let mut failures = Vec::new();

        self.validate_errors(stderr, &mut failures);
        self.validate_output(stdout, &mut failures);

        failures
    }

    fn run_script(&self, lang: LangLevel) -> (String, String) {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        match lang {
            LangLevel::Scanned => {
                let source = crox::scan(&self.content);
                for token in source {
                    match token {
                        Ok(t) => {
                            writeln!(&mut stdout, "{:?} {}", t.typ, source.slice(t.span)).unwrap();
                        }
                        Err(e) => unimplemented!("no negative tests: {e:?}"),
                    }
                }
            }
            LangLevel::Evaluated => {
                crox::run_as_evaluator(false, &mut stdout, &mut stderr, &self.content);
            }
            LangLevel::Interpreted | LangLevel::Compiled => {
                let _res = crox::run_as_script(false, &mut stdout, &mut stderr, &self.content);
            }
        };

        let stdout = String::from_utf8(stdout).unwrap();
        let stderr = String::from_utf8(stderr).unwrap();
        (stdout, stderr)
    }

    fn validate_errors(&self, stderr: String, failures: &mut Vec<String>) {
        let mut found_errors = HashSet::new();
        let mut unexpected_errors = Vec::new();
        let mut err_lines = stderr
            .trim_end_matches('\n')
            .lines()
            .filter(|s| !s.is_empty());
        while let Some(line) = err_lines.next() {
            if let Some(m) = SYNTAX_ERROR.captures(line) {
                let line_no = m[1].parse().unwrap();
                let offset = m[2].parse().unwrap();
                let actual = &m[3];

                if let Some(e) = self.expected_errors.iter().find(|e| e.line == line_no) {
                    found_errors.insert(e.clone());

                    if e.error != actual {
                        let cmp = pretty_assertions::StrComparison::new(&e.error, actual);
                        failures.push(format!(
                            "Different error on line {}: (expected, actual): {}",
                            line_no, cmp
                        ));
                    }

                    if e.offset != offset {
                        failures.push(format!(
                            "Different offset on line {}: expected = {}, actual = {}",
                            line_no, e.offset, offset
                        ));
                    }

                    if err_lines.next().is_none() {
                        failures
                            .push("Missing error line describing the original source".to_owned());
                    }

                    let error_msg = match err_lines.next() {
                        Some(line) => match line.chars().position(|c| c == '^') {
                            Some(idx) if idx == e.offset => continue,
                            Some(idx) => format!("Wrong caret position, expected it at index {} but got it at index {}", e.offset, idx),
                            None => "Caret line has not caret".to_owned(),
                        },
                        None => "Missing caret line".to_owned(),
                    };
                    failures.push(error_msg);
                    continue;
                }
            }
            unexpected_errors.push(line);
        }

        for unexpected in unexpected_errors.iter().take(10) {
            failures.push(format!("Unexpected error: {unexpected}"));
        }
        if let Some(more) = unexpected_errors.len().checked_sub(10) {
            if more > 0 {
                failures.push(format!("(truncated {more} more...)"));
            }
        }
        for missing in self.expected_errors.difference(&found_errors) {
            failures.push(format!(
                "Missing expected error: [{}] {}",
                missing.line, missing.error
            ));
        }
    }

    fn validate_output(&self, stdout: String, failures: &mut Vec<String>) {
        let mut output = stdout
            .trim_end_matches('\n')
            .lines()
            .filter(|s| !s.is_empty());
        let mut expected = self.expected_outputs.iter();
        for (line, expected) in output.by_ref().zip(expected.by_ref()) {
            if expected.output != line {
                let cmp = pretty_assertions::StrComparison::new(&expected.output, line);
                failures.push(format!(
                    "Different output on line {}: (expected, actual): {}",
                    expected.line, cmp,
                ));
            }
        }
        for line in output {
            failures.push(format!("Got output when none was expected: {line}"));
        }
        for expected in expected {
            failures.push(format!(
                "Missing expected output '{}' on line {}",
                expected.output, expected.line
            ));
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TestResult {
    Unknown(PathBuf),
    Missing(PathBuf),
    MixedErrorAssertions(PathBuf, (u32, u32)),
    Skipped,
    NotATest,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpectedOutput {
    line: usize,
    output: String,
}

impl ExpectedOutput {
    pub fn new(line: usize, output: impl Into<String>) -> Self {
        Self {
            line,
            output: output.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpectedError {
    error: String,
    line: usize,
    offset: usize,
    exit_code: u32,
}

impl ExpectedError {
    pub fn new(error: impl Into<String>, line: usize, offset: usize, exit_code: u32) -> Self {
        Self {
            error: error.into(),
            line,
            offset,
            exit_code,
        }
    }
}

#[cfg(test)]
mod units {
    use super::*;

    #[test]
    fn test_parse_expected_output() {
        let line = "// expect: foo";
        let actual = Test::parse_line(line, 1, LangLevel::Interpreted)
            .expect("An expectation")
            .expect("A valid expectation")
            .expect("An output expectation");
        assert_eq!(actual, ExpectedOutput::new(1, "foo".to_owned()));
    }

    #[test]
    fn test_parse_expected_error() {
        let line = "// [line 13, offset 37] Error: foo";
        let actual = Test::parse_line(line, 42, LangLevel::Interpreted)
            .expect("An expectation")
            .expect("A valid expectation")
            .expect_err("An error expectation");
        assert_eq!(actual, ExpectedError::new("foo".to_owned(), 13, 37, 65));
    }

    #[test]
    fn test_parse_expected_error_qualifier_is_optional() {
        let line = "// [line 13, offset 37] foo";
        let actual = Test::parse_line(line, 42, LangLevel::Interpreted)
            .expect("An expectation")
            .expect("A valid expectation")
            .expect_err("An error expectation");
        assert_eq!(actual, ExpectedError::new("foo".to_owned(), 13, 37, 65));
    }

    #[test]
    fn test_parse_expected_line_is_optional() {
        let line = "// [offset 37] Error: foo";
        let actual = Test::parse_line(line, 42, LangLevel::Interpreted)
            .expect("An expectation")
            .expect("A valid expectation")
            .expect_err("An error expectation");
        assert_eq!(actual, ExpectedError::new("foo".to_owned(), 42, 37, 65));
    }

    #[test]
    fn test_parse_expected_line_and_error_qualifier_are_optional() {
        let line = "// [offset 37] foo";
        let actual = Test::parse_line(line, 42, LangLevel::Interpreted)
            .expect("An expectation")
            .expect("A valid expectation")
            .expect_err("An error expectation");
        assert_eq!(actual, ExpectedError::new("foo".to_owned(), 42, 37, 65));
    }
}

use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

use crate::suites::{State, Suite};

use once_cell::sync::Lazy;
use regex::Regex;

macro_rules! re {
    ($s:literal) => {
        ::once_cell::sync::Lazy::new(|| ::regex::Regex::new($s).unwrap())
    };
}

static EXPECTED_OUTPUT: Lazy<Regex> = re!(r#"// expect: ?(.*)"#);
static EXPECTED_ERROR: Lazy<Regex> = re!(r#"// (Error.*)"#);
static ERROR_LINE: Lazy<Regex> = re!(r#"// \[((java|c) )?line (\d+)\] (Error.*)"#);
static EXPECTED_RUNTIME_ERROR: Lazy<Regex> = re!(r#"// expect runtime error: (.+)"#);
static SYNTAX_ERROR: Lazy<Regex> = re!(r#"\[.*line (\d+)\] (Error.+)"#);
static _STACK_TRACE: Lazy<Regex> = re!(r#"\[line (\d+)\]"#);
static NON_TEST: Lazy<Regex> = re!(r#"// nontest"#);

pub struct Test {
    path: PathBuf,
    content: String,
    expected_outputs: Vec<ExpectedOutput>,
    expected_errors: HashSet<ExpectedError>,
}

impl Test {
    pub fn parse(path: PathBuf, suite: &Suite) -> Result<Test, TestResult> {
        let mut subpaths = path
            .ancestors()
            .filter_map(|p| p.to_str())
            .filter(|p| !p.is_empty() && *p != "/")
            .collect::<Vec<_>>();
        subpaths.reverse();

        let mut state = None;
        for part in &subpaths {
            if let Some(s) = suite.tests.get(part) {
                state = Some(*s);
            }
        }

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

        for (line_no, line) in content.lines().enumerate() {
            let line_no = line_no + 1;

            if NON_TEST.is_match(line) {
                return Err(TestResult::NotATest);
            }

            if let Some(output) = EXPECTED_OUTPUT.captures(line) {
                expected_outputs.push(ExpectedOutput::new(line_no, output[1].to_owned()));
            } else if let Some(error) = EXPECTED_ERROR.captures(line) {
                expected_errors.insert(ExpectedError::new(error[1].to_owned(), line_no, 65));
            } else if let Some(error) = ERROR_LINE.captures(line) {
                if error.get(2).map_or(true, |l| l.as_str() == suite.lang) {
                    expected_errors.insert(ExpectedError::new(
                        error[4].to_owned(),
                        error[3].parse().unwrap(),
                        65,
                    ));
                }
            } else if let Some(error) = EXPECTED_RUNTIME_ERROR.captures(line) {
                expected_errors.insert(ExpectedError::new(error[1].to_owned(), line_no, 70));
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

    pub fn expectations(&self) -> usize {
        self.expected_outputs.len() + self.expected_errors.len()
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn run(&self) -> Vec<String> {
        let (stdout, stderr) = self.run_script();

        let mut failures = Vec::new();

        self.validate_errors(stderr, &mut failures);
        self.validate_output(stdout, &mut failures);

        failures
    }

    fn run_script(&self) -> (String, String) {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let _res = crox::run_as_script(false, &mut stdout, &mut stderr, &self.content);
        let stdout = String::from_utf8(stdout).unwrap();
        let stderr = String::from_utf8(stderr).unwrap();
        (stdout, stderr)
    }

    fn validate_errors(&self, stderr: String, failures: &mut Vec<String>) {
        let mut found_errors = HashSet::new();
        let mut unexpected_errors = Vec::new();
        for line in stderr
            .trim()
            .lines()
            .map(str::trim)
            .filter(|s| !s.is_empty())
        {
            if let Some(m) = SYNTAX_ERROR.captures(line) {
                let line_no = m[1].parse().unwrap();
                let msg = &m[2];

                if let Some(e) = self
                    .expected_errors
                    .iter()
                    .find(|e| e.line == line_no && e.error == msg)
                {
                    found_errors.insert(e.clone());
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
            .trim()
            .lines()
            .map(str::trim)
            .filter(|s| !s.is_empty());
        let mut expected = self.expected_outputs.iter();
        for (line, expected) in output.by_ref().zip(expected.by_ref()) {
            if expected.output != line {
                failures.push(format!(
                    "Expected output '{}' on line {}, but got '{}'",
                    expected.output, expected.line, line
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
    pub fn new(line: usize, output: String) -> Self {
        Self { line, output }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExpectedError {
    error: String,
    line: usize,
    exit_code: u32,
}

impl ExpectedError {
    pub fn new(error: String, line: usize, exit_code: u32) -> Self {
        Self {
            error,
            line,
            exit_code,
        }
    }
}

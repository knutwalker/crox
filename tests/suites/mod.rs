use std::collections::HashMap;

mod tests;
pub use tests::{ExpectedError, ExpectedOutput, Test, TestResult};
use walkdir::WalkDir;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LangLevel {
    Scanned,
    Evaluated,
    Interpreted,
    Compiled,
}

impl PartialEq<str> for LangLevel {
    fn eq(&self, other: &str) -> bool {
        match self {
            LangLevel::Evaluated | LangLevel::Scanned => false,
            LangLevel::Interpreted => other == "java",
            LangLevel::Compiled => other == "c",
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Run {
    Chapter4Scanning = 4,
    Chapter6Parsing = 6,
    Chapter7Evaluating = 7,
    Chapter8Statements = 8,
    Chapter9Control = 9,
    Chapter10Functions = 10,
    Chapter11Resolving = 11,
    Chapter12Classes = 12,
    Chapter13Inheritance = 13,
    AllInterpreted = 14,
    Chapter17Compiling = 17,
    Chapter18Types = 18,
    Chapter19Strings = 19,
    Chapter20Hash = 20,
    Chapter21Global = 21,
    Chapter22Local = 22,
    Chapter23Jumping = 23,
    Chapter24Calls = 24,
    Chapter25Closures = 25,
    Chapter26Garbage = 26,
    Chapter27Classes = 27,
    Chapter28Methods = 28,
    Chapter29Superclasses = 29,
    Chapter30Optimization = 30,
    AllCompiled = 31,
}

#[derive(Clone, Debug, Default)]
pub struct AllSuites {
    all: Vec<Option<Suite>>,
}

impl AllSuites {
    pub fn run(&self, select: Run) {
        let idx = usize::from(select as u8);

        let suite = self.all[idx]
            .as_ref()
            .expect("No suite defined for this chapter");

        println!(
            "=== Chapter {} {:?} ===",
            suite.chapter as u8, suite.chapter
        );

        if !suite.run() {
            panic!("There were test failures (see stderr)");
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum State {
    Skip,
    Pass,
}

#[derive(Clone, Debug)]
struct Suite {
    chapter: Run,
    lang: LangLevel,
    tests: HashMap<&'static str, State>,
}

impl Suite {
    fn new(chapter: Run, lang: LangLevel, tests: HashMap<&'static str, State>) -> Self {
        Self {
            chapter,
            lang,
            tests,
        }
    }

    fn run(&self) -> bool {
        let mut result = SuiteResult::default();

        let walker = WalkDir::new("tests").into_iter();
        let walker = walker
            .filter_entry(|e| {
                e.file_type().is_dir()
                    || e.path().extension().and_then(|e| e.to_str()) == Some("lox")
            })
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file());
        for entry in walker {
            Test::run_from(entry.path().to_path_buf(), self, &mut result);
        }

        if result.failed == 0 {
            println!(
                "\nAll {} tests passed ({} expectations).",
                result.passed, result.expectations
            );
            true
        } else {
            println!(
                "\n{} test passed. {} tests failed.",
                result.passed, result.failed
            );
            false
        }
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
struct SuiteResult {
    passed: usize,
    failed: usize,
    skipped: usize,
    expectations: usize,
}

impl AllSuites {
    fn insert(
        &mut self,
        chapter: Run,
        lang: LangLevel,
        tests: impl IntoIterator<Item = (&'static str, State)>,
    ) {
        let suite = Suite::new(chapter, lang, tests.into_iter().collect());
        let idx = usize::from(chapter as u8);
        if self.all.len() <= idx {
            self.all.resize(idx + 1, None);
        }
        self.all[idx] = Some(suite);
    }

    fn compiled(&mut self, chapter: Run, tests: impl IntoIterator<Item = (&'static str, State)>) {
        self.insert(chapter, LangLevel::Compiled, tests);
    }

    fn interpreted(
        &mut self,
        chapter: Run,
        tests: impl IntoIterator<Item = (&'static str, State)>,
    ) {
        self.insert(chapter, LangLevel::Interpreted, tests);
    }

    fn evaluated(&mut self, chapter: Run, tests: impl IntoIterator<Item = (&'static str, State)>) {
        self.insert(chapter, LangLevel::Evaluated, tests);
    }

    fn scanned(&mut self, chapter: Run, tests: impl IntoIterator<Item = (&'static str, State)>) {
        self.insert(chapter, LangLevel::Scanned, tests);
    }

    pub fn define() -> Self {
        type Tests<const N: usize> = [(&'static str, State); N];

        fn early_chapters() -> Tests<2> {
            [
                ("tests/scanning", State::Skip),
                ("tests/expressions", State::Skip),
            ]
        }

        // JVM doesn't correctly implement IEEE equality on boxed doubles.
        fn java_nan_equality() -> Tests<1> {
            [("tests/number/nan_equality.lox", State::Pass)]
        }

        // No hardcoded limits in jlox.
        fn no_java_limits() -> Tests<6> {
            [
                ("tests/limit/loop_too_large.lox", State::Skip),
                ("tests/limit/no_reuse_constants.lox", State::Skip),
                ("tests/limit/too_many_constants.lox", State::Skip),
                ("tests/limit/too_many_locals.lox", State::Skip),
                ("tests/limit/too_many_upvalues.lox", State::Skip),
                // Rely on JVM for stack overflow checking.
                ("tests/limit/stack_overflow.lox", State::Skip),
            ]
        }

        // No classes in Java yet.
        fn no_java_classes() -> Tests<18> {
            [
                ("tests/assignment/to_this.lox", State::Skip),
                ("tests/call/object.lox", State::Skip),
                ("tests/class", State::Skip),
                ("tests/closure/close_over_method_parameter.lox", State::Skip),
                ("tests/constructor", State::Skip),
                ("tests/field", State::Skip),
                ("tests/inheritance", State::Skip),
                ("tests/method", State::Skip),
                ("tests/number/decimal_point_at_eof.lox", State::Skip),
                ("tests/number/trailing_dot.lox", State::Skip),
                ("tests/operator/equals_class.lox", State::Skip),
                ("tests/operator/equals_method.lox", State::Skip),
                ("tests/operator/not_class.lox", State::Skip),
                ("tests/regression/394.lox", State::Skip),
                ("tests/super", State::Skip),
                ("tests/this", State::Skip),
                ("tests/return/in_method.lox", State::Skip),
                ("tests/variable/local_from_method.lox", State::Skip),
            ]
        }

        // No functions in Java yet.
        fn no_java_functions() -> Tests<14> {
            [
                ("tests/call", State::Skip),
                ("tests/closure", State::Skip),
                ("tests/for/closure_in_body.lox", State::Skip),
                ("tests/for/return_closure.lox", State::Skip),
                ("tests/for/return_inside.lox", State::Skip),
                ("tests/for/syntax.lox", State::Skip),
                ("tests/function", State::Skip),
                ("tests/operator/not.lox", State::Skip),
                ("tests/regression/40.lox", State::Skip),
                ("tests/return", State::Skip),
                ("tests/unexpected_character.lox", State::Skip),
                ("tests/while/closure_in_body.lox", State::Skip),
                ("tests/while/return_closure.lox", State::Skip),
                ("tests/while/return_inside.lox", State::Skip),
            ]
        }

        // No resolution in Java yet.
        fn no_java_resolution() -> Tests<8> {
            [
                ("tests/closure/assign_to_shadowed_later.lox", State::Skip),
                ("tests/function/local_mutual_recursion.lox", State::Skip),
                ("tests/variable/collide_with_parameter.lox", State::Skip),
                ("tests/variable/duplicate_local.lox", State::Skip),
                ("tests/variable/duplicate_parameter.lox", State::Skip),
                ("tests/variable/early_bound.lox", State::Skip),
                // Broken because we haven"t fixed it yet by detecting the error.
                ("tests/return/at_top_level.lox", State::Skip),
                ("tests/variable/use_local_in_initializer.lox", State::Skip),
            ]
        }

        // No control flow in C yet.
        fn no_c_control_flow() -> Tests<7> {
            [
                ("tests/block/empty.lox", State::Skip),
                ("tests/for", State::Skip),
                ("tests/if", State::Skip),
                ("tests/limit/loop_too_large.lox", State::Skip),
                ("tests/logical_operator", State::Skip),
                ("tests/variable/unreached_undefined.lox", State::Skip),
                ("tests/while", State::Skip),
            ]
        }

        // No functions in C yet.
        fn no_c_functions() -> Tests<21> {
            [
                ("tests/call", State::Skip),
                ("tests/closure", State::Skip),
                ("tests/for/closure_in_body.lox", State::Skip),
                ("tests/for/return_closure.lox", State::Skip),
                ("tests/for/return_inside.lox", State::Skip),
                ("tests/for/syntax.lox", State::Skip),
                ("tests/function", State::Skip),
                ("tests/limit/no_reuse_constants.lox", State::Skip),
                ("tests/limit/stack_overflow.lox", State::Skip),
                ("tests/limit/too_many_constants.lox", State::Skip),
                ("tests/limit/too_many_locals.lox", State::Skip),
                ("tests/limit/too_many_upvalues.lox", State::Skip),
                ("tests/regression/40.lox", State::Skip),
                ("tests/return", State::Skip),
                ("tests/unexpected_character.lox", State::Skip),
                ("tests/variable/collide_with_parameter.lox", State::Skip),
                ("tests/variable/duplicate_parameter.lox", State::Skip),
                ("tests/variable/early_bound.lox", State::Skip),
                ("tests/while/closure_in_body.lox", State::Skip),
                ("tests/while/return_closure.lox", State::Skip),
                ("tests/while/return_inside.lox", State::Skip),
            ]
        }

        // No classes in C yet.
        fn no_c_classes() -> Tests<19> {
            [
                ("tests/assignment/to_this.lox", State::Skip),
                ("tests/call/object.lox", State::Skip),
                ("tests/class", State::Skip),
                ("tests/closure/close_over_method_parameter.lox", State::Skip),
                ("tests/constructor", State::Skip),
                ("tests/field", State::Skip),
                ("tests/inheritance", State::Skip),
                ("tests/method", State::Skip),
                ("tests/number/decimal_point_at_eof.lox", State::Skip),
                ("tests/number/trailing_dot.lox", State::Skip),
                ("tests/operator/equals_class.lox", State::Skip),
                ("tests/operator/equals_method.lox", State::Skip),
                ("tests/operator/not.lox", State::Skip),
                ("tests/operator/not_class.lox", State::Skip),
                ("tests/regression/394.lox", State::Skip),
                ("tests/return/in_method.lox", State::Skip),
                ("tests/super", State::Skip),
                ("tests/this", State::Skip),
                ("tests/variable/local_from_method.lox", State::Skip),
            ]
        }

        // No inheritance in C yet.
        fn no_c_inheritance() -> Tests<7> {
            [
                ("tests/class/local_inherit_other.lox", State::Skip),
                ("tests/class/local_inherit_self.lox", State::Skip),
                ("tests/class/inherit_self.lox", State::Skip),
                ("tests/class/inherited_method.lox", State::Skip),
                ("tests/inheritance", State::Skip),
                ("tests/regression/394.lox", State::Skip),
                ("tests/super", State::Skip),
            ]
        }

        let mut suites = AllSuites::default();

        suites.scanned(
            Run::Chapter4Scanning,
            [
                // No interpreter yet.
                ("tests", State::Skip),
                ("tests/scanning", State::Pass),
            ]
            .into_iter(),
        );

        suites.evaluated(
            Run::Chapter6Parsing,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/parse.lox", State::Pass),
            ],
        );

        suites.evaluated(
            Run::Chapter7Evaluating,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.interpreted(
            Run::Chapter8Statements,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_functions())
                .chain(no_java_resolution())
                .chain(no_java_classes())
                .chain([
                    // No control flow.
                    ("tests/block/empty.lox", State::Skip),
                    ("tests/for", State::Skip),
                    ("tests/if", State::Skip),
                    ("tests/logical_operator", State::Skip),
                    ("tests/while", State::Skip),
                    ("tests/variable/unreached_undefined.lox", State::Skip),
                ]),
        );

        suites.interpreted(
            Run::Chapter9Control,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_functions())
                .chain(no_java_resolution())
                .chain(no_java_classes()),
        );

        suites.interpreted(
            Run::Chapter10Functions,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_resolution())
                .chain(no_java_classes()),
        );

        suites.interpreted(
            Run::Chapter11Resolving,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_classes()),
        );

        suites.interpreted(
            Run::Chapter12Classes,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_java_limits())
                .chain(java_nan_equality())
                .chain([
                    // No inheritance.
                    ("tests/class/local_inherit_other.lox", State::Skip),
                    ("tests/class/local_inherit_self.lox", State::Skip),
                    ("tests/class/inherit_self.lox", State::Skip),
                    ("tests/class/inherited_method.lox", State::Skip),
                    ("tests/inheritance", State::Skip),
                    ("tests/regression/394.lox", State::Skip),
                    ("tests/super", State::Skip),
                ]),
        );

        suites.interpreted(
            Run::Chapter13Inheritance,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits()),
        );

        suites.interpreted(
            Run::AllInterpreted,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits()),
        );

        suites.compiled(
            Run::Chapter17Compiling,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Run::Chapter18Types,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Run::Chapter19Strings,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Run::Chapter20Hash,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Run::Chapter21Global,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_control_flow())
                .chain(no_c_functions())
                .chain(no_c_classes())
                .chain([
                    // No blocks.
                    ("tests/assignment/local.lox", State::Skip),
                    ("tests/variable/in_middle_of_block.lox", State::Skip),
                    ("tests/variable/in_nested_block.lox", State::Skip),
                    (
                        "tests/variable/scope_reuse_in_different_blocks.lox",
                        State::Skip,
                    ),
                    ("tests/variable/shadow_and_local.lox", State::Skip),
                    ("tests/variable/undefined_local.lox", State::Skip),
                    // No local variables.
                    ("tests/block/scope.lox", State::Skip),
                    ("tests/variable/duplicate_local.lox", State::Skip),
                    ("tests/variable/shadow_global.lox", State::Skip),
                    ("tests/variable/shadow_local.lox", State::Skip),
                    ("tests/variable/use_local_in_initializer.lox", State::Skip),
                ]),
        );

        suites.compiled(
            Run::Chapter22Local,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_control_flow())
                .chain(no_c_functions())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Run::Chapter23Jumping,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_functions())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Run::Chapter24Calls,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_classes())
                .chain([
                    // No closures.
                    ("tests/closure", State::Skip),
                    ("tests/for/closure_in_body.lox", State::Skip),
                    ("tests/for/return_closure.lox", State::Skip),
                    ("tests/function/local_recursion.lox", State::Skip),
                    ("tests/limit/too_many_upvalues.lox", State::Skip),
                    ("tests/regression/40.lox", State::Skip),
                    ("tests/while/closure_in_body.lox", State::Skip),
                    ("tests/while/return_closure.lox", State::Skip),
                ]),
        );

        suites.compiled(
            Run::Chapter25Closures,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Run::Chapter26Garbage,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Run::Chapter27Classes,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_inheritance())
                .chain([
                    // No methods.
                    ("tests/assignment/to_this.lox", State::Skip),
                    ("tests/class/local_reference_self.lox", State::Skip),
                    ("tests/class/reference_self.lox", State::Skip),
                    ("tests/closure/close_over_method_parameter.lox", State::Skip),
                    ("tests/constructor", State::Skip),
                    ("tests/field/get_and_set_method.lox", State::Skip),
                    ("tests/field/method.lox", State::Skip),
                    ("tests/field/method_binds_this.lox", State::Skip),
                    ("tests/method", State::Skip),
                    ("tests/operator/equals_class.lox", State::Skip),
                    ("tests/operator/equals_method.lox", State::Skip),
                    ("tests/return/in_method.lox", State::Skip),
                    ("tests/this", State::Skip),
                    ("tests/variable/local_from_method.lox", State::Skip),
                ]),
        );

        suites.compiled(
            Run::Chapter28Methods,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_inheritance()),
        );

        suites.compiled(
            Run::Chapter29Superclasses,
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );

        suites.compiled(
            Run::Chapter30Optimization,
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );

        suites.compiled(
            Run::AllCompiled,
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );

        suites
    }
}

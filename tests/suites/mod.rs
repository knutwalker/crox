use std::{
    collections::HashMap,
    ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive},
};

mod tests;
pub use tests::{ExpectedError, ExpectedOutput, Test, TestResult};

#[derive(Clone, Debug)]
pub struct Suite {
    pub chapter: Chapter,
    pub lang: LangLevel,
    pub tests: HashMap<&'static str, State>,
}

impl Suite {
    fn new(chapter: Chapter, lang: LangLevel, tests: HashMap<&'static str, State>) -> Self {
        Self {
            chapter,
            lang,
            tests,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LangLevel {
    Interpreted,
    Compiled,
}

impl PartialEq<str> for LangLevel {
    fn eq(&self, other: &str) -> bool {
        match self {
            LangLevel::Interpreted => other == "java",
            LangLevel::Compiled => other == "c",
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum State {
    Skip,
    Pass,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Chapter {
    Scanning = 4,
    Parsing = 6,
    Evaluating = 7,
    Statements = 8,
    Control = 9,
    Functions = 10,
    Resolving = 11,
    Classes = 12,
    Inheritance = 13,
    AllInterpreted = 14,
    Compiling = 17,
    Types = 18,
    Strings = 19,
    Hash = 20,
    Global = 21,
    Local = 22,
    Jumping = 23,
    Calls = 24,
    Closures = 25,
    Garbage = 26,
    Classes2 = 27,
    Methods = 28,
    Superclasses = 29,
    Optimization = 30,
    AllCompiled = 31,
    All = 32,
}

impl TryFrom<i32> for Chapter {
    type Error = ();

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        Ok(match value {
            4 => Self::Scanning,
            6 => Self::Parsing,
            7 => Self::Evaluating,
            8 => Self::Statements,
            9 => Self::Control,
            10 => Self::Functions,
            11 => Self::Resolving,
            12 => Self::Classes,
            13 => Self::Inheritance,
            14 => Self::AllInterpreted,
            17 => Self::Compiling,
            18 => Self::Types,
            19 => Self::Strings,
            20 => Self::Hash,
            21 => Self::Global,
            22 => Self::Local,
            23 => Self::Jumping,
            24 => Self::Calls,
            25 => Self::Closures,
            26 => Self::Garbage,
            27 => Self::Classes2,
            28 => Self::Methods,
            29 => Self::Superclasses,
            30 => Self::Optimization,
            31 => Self::AllCompiled,
            32 => Self::All,
            _ => return Err(()),
        })
    }
}

pub trait ChapterSelect {
    fn select(&self, suite: &Suite) -> bool;
}

impl ChapterSelect for Chapter {
    fn select(&self, suite: &Suite) -> bool {
        self == &suite.chapter
    }
}

impl<const N: usize> ChapterSelect for [Chapter; N] {
    fn select(&self, suite: &Suite) -> bool {
        self.iter().any(|c| c.select(suite))
    }
}

impl ChapterSelect for LangLevel {
    fn select(&self, suite: &Suite) -> bool {
        self == &suite.lang
    }
}

impl ChapterSelect for i32 {
    fn select(&self, suite: &Suite) -> bool {
        if let Ok(chapter) = Chapter::try_from(*self) {
            chapter.select(suite)
        } else {
            false
        }
    }
}

impl ChapterSelect for RangeFull {
    fn select(&self, _suite: &Suite) -> bool {
        true
    }
}

impl ChapterSelect for Range<i32> {
    fn select(&self, suite: &Suite) -> bool {
        self.contains(&i32::from(suite.chapter as u8))
    }
}

impl ChapterSelect for RangeInclusive<i32> {
    fn select(&self, suite: &Suite) -> bool {
        self.contains(&i32::from(suite.chapter as u8))
    }
}

impl ChapterSelect for RangeFrom<i32> {
    fn select(&self, suite: &Suite) -> bool {
        self.contains(&i32::from(suite.chapter as u8))
    }
}

impl ChapterSelect for RangeTo<i32> {
    fn select(&self, suite: &Suite) -> bool {
        self.contains(&i32::from(suite.chapter as u8))
    }
}

impl ChapterSelect for RangeToInclusive<i32> {
    fn select(&self, suite: &Suite) -> bool {
        self.contains(&i32::from(suite.chapter as u8))
    }
}

#[derive(Clone, Debug, Default)]
pub struct AllSuites {
    all: Vec<Suite>,
}

impl AllSuites {
    pub fn get(&self, select: impl ChapterSelect) -> Vec<&Suite> {
        self.all.iter().filter(|s| select.select(s)).collect()
    }

    fn compiled(
        &mut self,
        chapter: Chapter,
        tests: impl IntoIterator<Item = (&'static str, State)>,
    ) {
        let suite = Suite::new(chapter, LangLevel::Compiled, tests.into_iter().collect());
        self.all.push(suite);
    }

    fn interpreted(
        &mut self,
        chapter: Chapter,
        tests: impl IntoIterator<Item = (&'static str, State)>,
    ) {
        let suite = Suite::new(chapter, LangLevel::Interpreted, tests.into_iter().collect());
        self.all.push(suite);
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
            [("tests/number/nan_equality.lox", State::Skip)]
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

        suites.interpreted(
            Chapter::AllInterpreted,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits()),
        );

        suites.interpreted(
            Chapter::Scanning,
            [
                // No interpreter yet.
                ("tests", State::Skip),
                ("tests/scanning", State::Pass),
            ]
            .into_iter(),
        );

        // No test for chapter 5. It just has a hardcoded main() in AstPrinter.

        suites.interpreted(
            Chapter::Parsing,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/parse.lox", State::Pass),
            ],
        );

        suites.interpreted(
            Chapter::Evaluating,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.interpreted(
            Chapter::Statements,
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
            Chapter::Control,
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
            Chapter::Functions,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_resolution())
                .chain(no_java_classes()),
        );

        suites.interpreted(
            Chapter::Compiling,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_classes()),
        );

        suites.interpreted(
            Chapter::Classes,
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
            Chapter::Inheritance,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits()),
        );

        suites.compiled(
            Chapter::AllCompiled,
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );

        suites.compiled(
            Chapter::Compiling,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Chapter::Types,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Chapter::Strings,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Chapter::Hash,
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.compiled(
            Chapter::Global,
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
            Chapter::Local,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_control_flow())
                .chain(no_c_functions())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Chapter::Jumping,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_functions())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Chapter::Calls,
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
            Chapter::Closures,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Chapter::Garbage,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_classes()),
        );

        suites.compiled(
            Chapter::Classes2,
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
            Chapter::Methods,
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_inheritance()),
        );

        suites.compiled(
            Chapter::Superclasses,
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );

        suites.compiled(
            Chapter::Optimization,
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );
        suites
    }
}

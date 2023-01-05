use std::collections::HashMap;

mod tests;
pub use tests::{ExpectedError, ExpectedOutput, Test, TestResult};

#[derive(Clone, Debug)]
pub struct Suite {
    pub name: String,
    pub lang: String,
    pub executable: String,
    pub args: Vec<String>,
    pub tests: HashMap<&'static str, State>,
}

impl Suite {
    fn new(
        name: impl Into<String>,
        lang: impl Into<String>,
        executable: impl Into<String>,
        args: Vec<String>,
        tests: HashMap<&'static str, State>,
    ) -> Self {
        Self {
            name: name.into(),
            lang: lang.into(),
            executable: executable.into(),
            args,
            tests,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum State {
    Skip,
    Pass,
}

#[derive(Clone, Debug, Default)]
pub struct AllSuites {
    all: HashMap<&'static str, Suite>,
}

impl AllSuites {
    pub fn get(&self, name: &str) -> Vec<&Suite> {
        match name {
            "all" => self.all.values().collect(),
            "c" => self.all.values().filter(|s| s.lang == "c").collect(),
            "java" => self.all.values().filter(|s| s.lang == "java").collect(),
            otherwise => vec![&self.all[otherwise]],
        }
    }

    fn c(&mut self, name: &'static str, tests: impl IntoIterator<Item = (&'static str, State)>) {
        let executable = "cargo run -- ";
        let suite = Suite::new(
            name,
            "c",
            executable,
            Vec::new(),
            tests.into_iter().collect(),
        );
        self.all.insert(name, suite);
    }

    fn java(&mut self, name: &'static str, tests: impl IntoIterator<Item = (&'static str, State)>) {
        let executable = "cargo run -- ";
        let suite = Suite::new(
            name,
            "java",
            executable,
            Vec::new(),
            tests.into_iter().collect(),
        );

        self.all.insert(name, suite);
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

        suites.java(
            "jlox",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits()),
        );

        suites.java(
            "chap04_scanning",
            [
                // No interpreter yet.
                ("tests", State::Skip),
                ("tests/scanning", State::Pass),
            ]
            .into_iter(),
        );

        // No test for chapter 5. It just has a hardcoded main() in AstPrinter.

        suites.java(
            "chap06_parsing",
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/parse.lox", State::Pass),
            ],
        );

        suites.java(
            "chap07_evaluating",
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.java(
            "chap08_statements",
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

        suites.java(
            "chap09_control",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_functions())
                .chain(no_java_resolution())
                .chain(no_java_classes()),
        );

        suites.java(
            "chap10_functions",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_resolution())
                .chain(no_java_classes()),
        );

        suites.java(
            "chap11_resolving",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits())
                .chain(no_java_classes()),
        );

        suites.java(
            "chap12_classes",
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

        suites.java(
            "chap13_inheritance",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(java_nan_equality())
                .chain(no_java_limits()),
        );

        suites.c(
            "clox",
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );

        suites.c(
            "chap17_compiling",
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.c(
            "chap18_types",
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.c(
            "chap19_strings",
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.c(
            "chap20_hash",
            [
                // No real interpreter yet.
                ("tests", State::Skip),
                ("tests/expressions/evaluate.lox", State::Pass),
            ],
        );

        suites.c(
            "chap21_global",
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

        suites.c(
            "chap22_local",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_control_flow())
                .chain(no_c_functions())
                .chain(no_c_classes()),
        );

        suites.c(
            "chap23_jumping",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_functions())
                .chain(no_c_classes()),
        );

        suites.c(
            "chap24_calls",
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

        suites.c(
            "chap25_closures",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_classes()),
        );

        suites.c(
            "chap26_garbage",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_classes()),
        );

        suites.c(
            "chap27_classes",
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

        suites.c(
            "chap28_methods",
            [("tests", State::Pass)]
                .into_iter()
                .chain(early_chapters())
                .chain(no_c_inheritance()),
        );

        suites.c(
            "chap29_superclasses",
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );

        suites.c(
            "chap30_optimization",
            [("tests", State::Pass)].into_iter().chain(early_chapters()),
        );
        suites
    }
}

# List available recipes
default:
    @just --list --unsorted

# Debug REPL
repl:
    cargo run

# Release REPL
replr:
    cargo run --release

# Run a lox script
run file:
    cargo run -- {{file}}

# Run a lox script in release mode
runr file:
    cargo run --release -- {{file}}

test:
    cargo test

# Continuously test
ctest:
    cargo watch -x test

# Continuously test with nvim integration
ltest:
    cargo watch -x 'ltest -- --nocapture'

# Run benchmark of the parser
bench-parser:
    cargo bench -- Parser

# Run a specific benchmark (pass path to file in tests/benchmark/*)
bench bench:
    cargo bench -- 'Benches/{{ if path_exists(bench) == "true" { file_stem(bench) } else { bench } }}'

# Extensive benchmarks (might take an hour)
bench-all: bench-parser
    cargo bench -- 'Benches/binary_trees'
    cargc bench -- 'Benches/equality'
    cargc bench -- 'Benches/fib'
    cargc bench -- 'Benches/instantiation'
    cargc bench -- 'Benches/invocation'
    cargc bench -- 'Benches/method_call'
    cargc bench -- 'Benches/properties'
    cargc bench -- 'Benches/string_equality'
    cargc bench -- 'Benches/trees'
    cargc bench -- 'Benches/zoo'
    cargc bench -- 'Benches/zoo_batch'

# Generate flamegraphs for parser benchmark
flame-parser:
    cargo flamegraph --bench parser --root -- --bench --profile-time 5

# Generate flamegraphs for a specific benchmark (pass path to file in tests/benchmark/*)
flame bench:
    cargo flamegraph --bench crox --root -- --bench 'Benches/{{ if path_exists(bench) == "true" { file_stem(bench) } else { bench } }}' --profile-time 5


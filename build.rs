use std::env;
use std::fs;
use std::path::Path;
use std::process::{Command, ExitStatus};
use std::str;

// Check if the currenct toolchain can compile a benchmark.
// If so, we enable the benchmarks.
const BENCH_PROBE: &str = r#"
#![feature(test)]

extern crate test;

use test::Bencher;

#[bench]
fn bench(b: &mut Bencher) {
    b.iter(|| 42);
}
"#;

fn main() {
    match compile_probe(BENCH_PROBE) {
        Some(status) if status.success() => println!("cargo:rustc-cfg=benches"),
        _ => {}
    }
}

fn compile_probe(probe: &str) -> Option<ExitStatus> {
    let rustc = env::var_os("RUSTC")?;
    let out_dir = env::var_os("OUT_DIR")?;
    let probefile = Path::new(&out_dir).join("probe.rs");
    fs::write(&probefile, probe).ok()?;
    Command::new(rustc)
        .arg("--edition=2021")
        .arg("--crate-name=crox_build")
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("--out-dir")
        .arg(out_dir)
        .arg(probefile)
        .status()
        .ok()
}

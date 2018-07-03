extern crate bindgen;
extern crate cc;

use std::{env, fs, path};

// Downloaded from http://www.netlib.org/misc/intel/
const DFP_PATH: &str = "IntelRDFPMathLib20U2/";

fn bindgen() {
    let bindings = bindgen::Builder::default()
        .header("src/bindings.h")
        //.ctypes_prefix("libc")
        .generate()
        .expect("unable to generate Intel(R) Decimal Floating-Point Math Library bindings");

    let out_path = path::PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("unable to write Intel(R) Decimal Floating-Point Math Library bindings");
}

fn compile() {
    let mut config = cc::Build::new();
    config
        .define("DECIMAL_CALL_BY_REFERENCE", "0")
        .define("DECIMAL_GLOBAL_ROUNDING", "0")
        .define("DECIMAL_GLOBAL_EXCEPTION_FLAGS", "0");

    for entry in fs::read_dir(format!("{}LIBRARY/src", DFP_PATH)).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map_or(false, |s| s == "c") {
            config.file(path);
        }
    }

    if cfg!(not(target_env = "msvc")) {
        config.flag("-Wno-dangling-else");
        config.flag("-Wno-implicit-function-declaration");
    }

    config.warnings(false).extra_warnings(false).compile("bid");
}

fn main() {
    println!("cargo:rerun-if-changed={}", DFP_PATH);
    bindgen();
    compile();
}

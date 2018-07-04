extern crate bindgen;
extern crate cc;

use std::{env, fs, path};

// Downloaded from http://www.netlib.org/misc/intel/
const DFP_PATH: &str = "IntelRDFPMathLib20U2/";

const F128_SOURCES: [&str; 19] = [
    "dpml_exception.c",
    "dpml_four_over_pi.c",
    "dpml_ux_bessel.c",
    "dpml_ux_bid.c",
    "dpml_ux_cbrt.c",
    "dpml_ux_erf.c",
    "dpml_ux_exp.c",
    "dpml_ux_int.c",
    "dpml_ux_inv_hyper.c",
    "dpml_ux_inv_trig.c",
    "dpml_ux_lgamma.c",
    "dpml_ux_log.c",
    "dpml_ux_mod.c",
    "dpml_ux_ops.c",
    "dpml_ux_ops_64.c",
    "dpml_ux_pow.c",
    "dpml_ux_powi.c",
    "dpml_ux_sqrt.c",
    "dpml_ux_trig.c",
];

fn bindgen() {
    let bindings = bindgen::Builder::default()
        .header("src/bindings.h")
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

    if cfg!(target_pointer_width = "32") {
        config.define("ia32", "1");
    } else if cfg!(target_pointer_width = "64") {
        config.define("efi2", "1");
    } else {
        panic!("architecture not supported")
    }

    // Collect all the sources
    for entry in fs::read_dir(format!("{}LIBRARY/src", DFP_PATH)).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().map_or(false, |s| s == "c")
            && !path
                .file_name()
                .map_or(false, |s| s == "bid_decimal_globals.c")
        {
            config.file(path);
        }
    }

    for src in &F128_SOURCES {
        config.file(format!("{}LIBRARY/float128/{}", DFP_PATH, src));
    }

    if cfg!(not(target_env = "msvc")) {
        config
            .flag("-Wno-dangling-else")
            .flag("-Wno-implicit-function-declaration")
            .flag("-Wno-constant-conversion")
            .flag("-Wno-shift-negative-value")
            .flag("-Wno-comment")
            .flag("-Wno-parentheses");
    }

    config.warnings(false).extra_warnings(false).compile("bid");
}

fn main() {
    bindgen();
    compile();
}

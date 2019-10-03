use std::io::Write;

fn main() {
    let d128 = std::fs::read_to_string("src/d32_impl.rs").unwrap();

    // Generate d64.rs
    let d64 = d128.replace("u32", "u64");
    let mut d64_out = std::fs::File::create("src/d64_impl.rs").unwrap();
    writeln!(
        d64_out,
        "// **NOTE**: THIS FILE IS AUTO-GENERATED FROM d32_impl.rs. DO NOT MODIFY!"
    )
    .unwrap();
    d64_out.write_all(d64.as_bytes()).unwrap();

    // Generate d128.rs
    let d32 = d128.replace("u32", "u128");
    let mut d128_out = std::fs::File::create("src/d128_impl.rs").unwrap();
    writeln!(
        d128_out,
        "// **NOTE**: THIS FILE IS AUTO-GENERATED FROM d32_impl.rs. DO NOT MODIFY!"
    )
    .unwrap();
    d128_out.write_all(d32.as_bytes()).unwrap();
}

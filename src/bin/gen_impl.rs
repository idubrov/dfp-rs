use std::io::Write;

fn main() {
    let d128 = std::fs::read_to_string("src/d128_impl.rs").unwrap();

    // Generate d64.rs
    let d64 = d128
        .replace("Decimal128", "Decimal64")
        .replace("u128", "u64");
    let mut d64_out = std::fs::File::create("src/d64_impl.rs").unwrap();
    writeln!(
        d64_out,
        "// **NOTE**: THIS FILE IS AUTO-GENERATED FROM d128_impl.rs. DO NOT MODIFY!"
    )
    .unwrap();
    d64_out.write_all(d64.as_bytes()).unwrap();

    // Generate d32.rs
    let d32 = d128
        .replace("Decimal128", "Decimal32")
        .replace("u128", "u32");
    let mut d32_out = std::fs::File::create("src/d32_impl.rs").unwrap();
    writeln!(
        d32_out,
        "// **NOTE**: THIS FILE IS AUTO-GENERATED FROM d128_impl.rs. DO NOT MODIFY!"
    )
    .unwrap();
    d32_out.write_all(d32.as_bytes()).unwrap();
}

extern crate dfp;

use dfp::{Rounding, Status, FpCategory};
use std::collections::BTreeMap;
use std::error;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};

type Result<T> = std::result::Result<T, Box<error::Error>>;

fn read_spec() -> impl Iterator<Item = Result<String>> {
    let spec = File::open("./spec/readtest.in").unwrap();
    let spec = BufReader::new(spec);

    spec.lines()
        .map(|line| {
            let mut line = line?;
            // Strip comments
            let eol = line.find("--").unwrap_or(line.len());
            line.truncate(eol);
            Ok(line)
        }).filter(|line| line.as_ref().map(|l| !l.trim().is_empty()).unwrap_or(true))
}

struct TestCase {
    func: String,
    rounding: Rounding,
    status: Status,
    assert: String,
}

fn parse_rounding(rnd: &str) -> Rounding {
    match rnd {
        "0" => Rounding::Nearest,
        "1" => Rounding::Down,
        "2" => Rounding::Up,
        "3" => Rounding::Zero,
        "4" => Rounding::TiesAway,
        _ => panic!("unknown rounding: '{}'", rnd),
    }
}

fn parse_class(rnd: &str) -> FpCategory {
    match rnd {
        "0" | "1" => FpCategory::Nan,
        "2" | "9" => FpCategory::Infinite,
        "3" | "8" => FpCategory::Normal,
        "4" | "7" => FpCategory::Subnormal,
        "5" | "6" => FpCategory::Zero,
        _ => panic!("unknown category: '{}'", rnd),
    }
}

fn scan_str<'a>(iter: &mut &'a str) -> Option<&'a str> {
    *iter = iter.trim_left();
    let pos = iter.find(char::is_whitespace)?;
    let res = &iter[..pos];
    *iter = iter[pos..].trim_left();
    Some(res)
}

fn scan_decimal(iter: &mut &str, ty: &str) -> Option<String> {
    let value = scan_str(iter)?;
    if value.starts_with('[') && value.ends_with(']') {
        let value = &value[1..value.len() - 1].replace(',', "");
        Some(format!("{}::from_bits(0x{})", ty, value))
    } else {
        None
        // FIXME: re-enable when we start supporting parsing numbers
        //Some(format!("\"{}\".parse::<{}>().unwrap()", value, ty))
    }
}

fn scan_bool(iter: &mut &str) -> Option<bool> {
    let value = scan_str(iter)?;
    if value == "0" {
        Some(false)
    } else if value == "1" {
        Some(true)
    } else {
        panic!("unexpected boolean value: '{}'", value)
    }
}

fn scan_status(iter: &mut &str) -> Option<u8> {
    let mut status = scan_str(iter)?;
    if status.starts_with("0x") {
        status = &status[2..];
    }
    Some(
        status
            .parse::<u8>()
            .unwrap_or_else(|_| panic!("invalid status: '{}'", status)),
    )
}

fn parse_boolean_op(ty: &str, func: &str, mut spec: &str) -> Option<String> {
    let arg0 = scan_decimal(&mut spec, ty)?;
    let result = scan_bool(&mut spec)?;
    let _status = scan_status(&mut spec);
    let prefix = if result { "" } else { "!" };
    Some(format!("assert!({}{}.{}());", prefix, arg0, func))
}

fn parse_unary_op(ty: &str, func: &str, mut spec: &str) -> Option<String> {
    let arg0 = scan_decimal(&mut spec, ty)?;
    let result = scan_decimal(&mut spec, ty)?;
    let _status = scan_status(&mut spec);
    Some(format!("assert_eq!({}.{}().to_bits(), {}.to_bits());", arg0, func, result))
}

fn parse_classify_op(ty: &str, mut spec: &str) -> Option<String> {
    let arg0 = scan_decimal(&mut spec, ty)?;
    let category_str = scan_str(&mut spec)?;
    let category = parse_class(category_str);
    let _status = scan_status(&mut spec);
    Some(format!("assert_eq!({}.classify(), FpCategory::{:?});", arg0, category))
}

fn parse_case(func: &str, spec: &str) -> Option<String> {
    match func {
        "bid32_isNaN" => parse_boolean_op("d32", "is_nan", spec),
        "bid64_isNaN" => parse_boolean_op("d64", "is_nan", spec),
        "bid128_isNaN" => parse_boolean_op("d128", "is_nan", spec),

        "bid32_isInf" => parse_boolean_op("d32", "is_infinite", spec),
        "bid64_isInf" => parse_boolean_op("d64", "is_infinite", spec),
        "bid128_isInf" => parse_boolean_op("d128", "is_infinite", spec),

        "bid32_isFinite" => parse_boolean_op("d32", "is_finite", spec),
        "bid64_isFinite" => parse_boolean_op("d64", "is_finite", spec),
        "bid128_isFinite" => parse_boolean_op("d128", "is_finite", spec),

        "bid32_isNormal" => parse_boolean_op("d32", "is_normal", spec),
        "bid64_isNormal" => parse_boolean_op("d64", "is_normal", spec),
        "bid128_isNormal" => parse_boolean_op("d128", "is_normal", spec),

        "bid32_isSubnormal" => parse_boolean_op("d32", "is_subnormal", spec),
        "bid64_isSubnormal" => parse_boolean_op("d64", "is_subnormal", spec),
        "bid128_isSubnormal" => parse_boolean_op("d128", "is_subnormal", spec),

        "bid32_isSigned" => parse_boolean_op("d32", "is_sign_negative", spec),
        "bid64_isSigned" => parse_boolean_op("d64", "is_sign_negative", spec),
        "bid128_isSigned" => parse_boolean_op("d128", "is_sign_negative", spec),

        "bid32_class" => parse_classify_op("d32", spec),
        "bid64_class" => parse_classify_op("d64", spec),
        "bid128_class" => parse_classify_op("d128", spec),

        "bid32_abs" => parse_unary_op("d32", "abs", spec),
        "bid64_abs" => parse_unary_op("d64", "abs", spec),
        "bid128_abs" => parse_unary_op("d128", "abs", spec),

        _ => None,
    }
}

fn parse_spec(line: String) -> Option<TestCase> {
    let mut iter = line.as_str();
    let func = scan_str(&mut iter)?;
    let rounding = scan_str(&mut iter)?;
    let rounding = parse_rounding(rounding);
    let assert = parse_case(&func, iter)?;

    Some(TestCase {
        func: func.to_owned(),
        rounding,
        status: Status::from_bits(0),
        assert,
    })
}

fn main() -> Result<()> {
    let mut cases = BTreeMap::new();
    for line in read_spec() {
        let case = parse_spec(line?);
        if let Some(case) = case {
            cases
                .entry(case.func.clone())
                .or_insert_with(Vec::new)
                .push(case);
        }
    }

    let mut out = BufWriter::new(File::create("tests/tests.rs")?);
    writeln!(out, "//! AUTOGENERATED. DO NOT EDIT")?;
    writeln!(out, "#![allow(non_snake_case)]")?;
    writeln!(out, "extern crate dfp;")?;
    writeln!(out)?;
    writeln!(out, "use dfp::{{d32, d64, d128, FpCategory}};")?;
    writeln!(out)?;

    for (key, cases) in cases {
        writeln!(out, "#[test]")?;
        writeln!(out, "fn {}() {{", key)?;
        for case in cases {
            // FIXME: rounding...
            writeln!(out, "    {}", case.assert)?;
        }
        writeln!(out, "}}")?;
        writeln!(out)?;
    }

    Ok(())
}

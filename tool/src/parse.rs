use dfp::{FpCategory, Rounding, Status};
use std::fmt;
use std::str::FromStr;

struct Parser<'a> {
    input: &'a str,
}

fn interpret_special(s: &str) -> String {
    // FIXME: test we handle both 1.0e+1 and 1.0E+1
    s.to_lowercase().replace("nan", "NaN").replace("NaNi", "NaN").replace("infinity", "inf")
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Parser { input }
    }

    fn parse_str(&mut self) -> &str {
        self.input = self.input.trim();
        let pos = self
            .input
            .find(char::is_whitespace)
            .unwrap_or_else(|| self.input.len());
        let res = &self.input[..pos];
        self.input = self.input[pos..].trim_start();
        res
    }

    fn parse_bool(&mut self) -> bool {
        match self.parse_str() {
            "0" => false,
            "1" => true,
            other => panic!("Invalid boolean value: `{}`", other),
        }
    }

    fn parse_rounding(&mut self) -> Rounding {
        match self.parse_str() {
            "0" => Rounding::Nearest,
            "1" => Rounding::Down,
            "2" => Rounding::Up,
            "3" => Rounding::Zero,
            "4" => Rounding::TiesAway,
            other => panic!("Invalid rounding: `{}`", other),
        }
    }

    fn parse_value(&mut self, format: DecimalType) -> DecimalArg {
        let value = self.parse_str();
        let representation = if value.starts_with('[') && value.ends_with(']') {
            let value = &value[1..value.len() - 1].replace(',', "");
            Representation::Bits(value.into())
        } else {
            Representation::Str(interpret_special(value))
        };

        DecimalArg {
            dec_type: format,
            representation,
        }
    }

    fn parse_status(&mut self) -> Status {
        let mut status = self.parse_str();
        if status.starts_with("0x") {
            status = &status[2..];
        }
        let status = u8::from_str_radix(status, 16)
            .unwrap_or_else(|_| panic!("Invalid status: `{}`", status));
        Status::from_bits(status)
    }

    // FIXME: support sign, too?
    /// Parse number category and sign; `true` is positive.
    fn parse_category_sign(&mut self) -> (FpCategory, bool) {
        match self.parse_str() {
            // Negative NaN is signaling NaN
            "0" => (FpCategory::Nan, false),
            "1" => (FpCategory::Nan, true),
            "2" => (FpCategory::Infinite, false),
            "3" => (FpCategory::Normal, false),
            "4" => (FpCategory::Subnormal, false),
            "5" => (FpCategory::Zero, false),
            "6" => (FpCategory::Zero, true),
            "7" => (FpCategory::Subnormal, true),
            "8" => (FpCategory::Normal, true),
            "9" => (FpCategory::Infinite, true),
            other => panic!("Invalid category: '{}'", other),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DecimalType {
    Decimal32,
    Decimal64,
    Decimal128,
}

impl fmt::Display for DecimalType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DecimalType::Decimal32 => f.write_str("d32"),
            DecimalType::Decimal64 => f.write_str("d64"),
            DecimalType::Decimal128 => f.write_str("d128"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct DecimalArg {
    pub dec_type: DecimalType,
    pub representation: Representation,
}

impl fmt::Display for DecimalArg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.representation {
            Representation::Bits(ref bits) => write!(f, "{}::from_bits(0x{})", self.dec_type, bits),
            Representation::Str(ref s) => {
                write!(f, "\"{}\".parse::<{}>().unwrap()", s, self.dec_type)
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Representation {
    Bits(String),
    Str(String),
}

#[derive(Debug, PartialEq)]
pub struct BoolOp {
    pub op: &'static str,
    pub arg0: DecimalArg,
    pub result: bool,
}

impl fmt::Display for BoolOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let prefix = if self.result { "" } else { "!" };
        write!(f, "assert!({}{}.{}());", prefix, self.arg0, self.op)
    }
}

impl BoolOp {
    fn parse(parser: &mut Parser, format: DecimalType, op: &'static str) -> TestCaseKind {
        let _rounding = parser.parse_rounding();
        TestCaseKind::Bool(BoolOp {
            op,
            arg0: parser.parse_value(format),
            result: parser.parse_bool(),
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct UnaryOp {
    pub op: &'static str,
    pub arg0: DecimalArg,
    pub result: DecimalArg,
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "assert_eq!(Bits({}.{}().to_bits()), Bits({}.to_bits()));",
            self.arg0, self.op, self.result
        )
    }
}

impl UnaryOp {
    fn parse(parser: &mut Parser, format: DecimalType, op: &'static str) -> TestCaseKind {
        let _rounding = parser.parse_rounding();
        TestCaseKind::Unary(UnaryOp {
            op,
            arg0: parser.parse_value(format),
            result: parser.parse_value(format),
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct ParseOp {
    pub rounding: Rounding,
    pub arg0: String,
    pub result: DecimalArg,
}

impl fmt::Display for ParseOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "assert_eq!(Bits({}::parse_rounding(\"{}\", Rounding::{:?}).unwrap_or({}::NAN).to_bits()), Bits({}.to_bits()));",
            self.result.dec_type, self.arg0, self.rounding, self.result.dec_type, self.result
        )
    }
}

impl ParseOp {
    fn parse(parser: &mut Parser, format: DecimalType) -> TestCaseKind {
        TestCaseKind::Parse(ParseOp {
            rounding: parser.parse_rounding(),
            arg0: interpret_special(parser.parse_str()),
            result: parser.parse_value(format),
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct ClassifyOp {
    pub value: DecimalArg,
    pub category: FpCategory,
    pub is_positive: bool,
}

impl fmt::Display for ClassifyOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "assert_eq!({}.classify(), FpCategory::{:?});",
            self.value, self.category
        )?;
        if self.category == FpCategory::Nan {
            if self.is_positive {
                write!(f, "    assert!(!{}.is_snan());", self.value)
            } else {
                write!(f, "    assert!({}.is_snan());", self.value)
            }
        } else if self.is_positive {
            write!(f, "    assert!({}.is_sign_positive());", self.value)
        } else {
            write!(f, "    assert!({}.is_sign_negative());", self.value)
        }

        // FIXME: sign!
    }
}

impl ClassifyOp {
    fn parse(parser: &mut Parser, format: DecimalType) -> TestCaseKind {
        let _rounding = parser.parse_rounding();
        let value = parser.parse_value(format);
        let (category, is_positive) = parser.parse_category_sign();
        TestCaseKind::Classify(ClassifyOp {
            value,
            category,
            is_positive,
        })
    }
}

#[derive(Debug, PartialEq)]
pub enum TestCaseKind {
    Bool(BoolOp),
    Unary(UnaryOp),
    Parse(ParseOp),
    Classify(ClassifyOp),
    Unsupported,
}

pub struct TestCase {
    pub op: String,
    pub status: Status,
    pub case: TestCaseKind,
}

impl FromStr for TestCase {
    type Err = ();

    fn from_str(s: &str) -> Result<TestCase, ()> {
        let parser = &mut Parser::new(s);
        let op = parser.parse_str().to_owned();
        let case = match op.as_str() {
            "bid32_isNaN" => BoolOp::parse(parser, DecimalType::Decimal32, "is_nan"),
            "bid64_isNaN" => BoolOp::parse(parser, DecimalType::Decimal64, "is_nan"),
            "bid128_isNaN" => BoolOp::parse(parser, DecimalType::Decimal128, "is_nan"),

            "bid32_isInf" => BoolOp::parse(parser, DecimalType::Decimal32, "is_infinite"),
            "bid64_isInf" => BoolOp::parse(parser, DecimalType::Decimal64, "is_infinite"),
            "bid128_isInf" => BoolOp::parse(parser, DecimalType::Decimal128, "is_infinite"),

            "bid32_isFinite" => BoolOp::parse(parser, DecimalType::Decimal32, "is_finite"),
            "bid64_isFinite" => BoolOp::parse(parser, DecimalType::Decimal64, "is_finite"),
            "bid128_isFinite" => BoolOp::parse(parser, DecimalType::Decimal128, "is_finite"),

            "bid32_isNormal" => BoolOp::parse(parser, DecimalType::Decimal32, "is_normal"),
            "bid64_isNormal" => BoolOp::parse(parser, DecimalType::Decimal64, "is_normal"),
            "bid128_isNormal" => BoolOp::parse(parser, DecimalType::Decimal128, "is_normal"),

            "bid32_isSubnormal" => BoolOp::parse(parser, DecimalType::Decimal32, "is_subnormal"),
            "bid64_isSubnormal" => BoolOp::parse(parser, DecimalType::Decimal64, "is_subnormal"),
            "bid128_isSubnormal" => BoolOp::parse(parser, DecimalType::Decimal128, "is_subnormal"),

            "bid32_isSigned" => BoolOp::parse(parser, DecimalType::Decimal32, "is_sign_negative"),
            "bid64_isSigned" => BoolOp::parse(parser, DecimalType::Decimal64, "is_sign_negative"),
            "bid128_isSigned" => BoolOp::parse(parser, DecimalType::Decimal128, "is_sign_negative"),

            "bid32_class" => ClassifyOp::parse(parser, DecimalType::Decimal32),
            "bid64_class" => ClassifyOp::parse(parser, DecimalType::Decimal64),
            "bid128_class" => ClassifyOp::parse(parser, DecimalType::Decimal128),

            "bid32_abs" => UnaryOp::parse(parser, DecimalType::Decimal32, "abs"),
            "bid64_abs" => UnaryOp::parse(parser, DecimalType::Decimal64, "abs"),
            "bid128_abs" => UnaryOp::parse(parser, DecimalType::Decimal128, "abs"),

            "bid32_from_string" => ParseOp::parse(parser, DecimalType::Decimal32),
            "bid64_from_string" => ParseOp::parse(parser, DecimalType::Decimal64),
            "bid128_from_string" => ParseOp::parse(parser, DecimalType::Decimal128),

            _ => {
                return Ok(TestCase {
                    op,
                    case: TestCaseKind::Unsupported,
                    status: Status::from_bits(0),
                })
            }
        };

        let status = parser.parse_status();
        Ok(TestCase { op, status, case })
    }
}

impl fmt::Display for TestCase {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.case {
            TestCaseKind::Bool(op) => op.fmt(f),
            TestCaseKind::Unary(op) => op.fmt(f),
            TestCaseKind::Parse(op) => op.fmt(f),
            TestCaseKind::Classify(op) => op.fmt(f),
            TestCaseKind::Unsupported => panic!("unsupported operation"),
        }
    }
}

impl TestCase {
    pub fn is_supported(&self) -> bool {
        match &self.case {
            TestCaseKind::Bool(op) => match op.arg0.representation {
                // FIXME: support once we can parse numbers!
                Representation::Str(_) => false,
                Representation::Bits(_) => true,
            },
            TestCaseKind::Unary(op) => match op.arg0.representation {
                // FIXME: support once we can parse numbers!
                Representation::Str(_) => false,
                Representation::Bits(_) => true,
            },
            TestCaseKind::Parse(op) => match op.result.representation {
                // FIXME: support once we can parse numbers!
                Representation::Str(_) => false,
                Representation::Bits(_) => true,
            },
            TestCaseKind::Classify(op) => match op.value.representation {
                // FIXME: support once we can parse numbers!
                Representation::Str(_) => false,
                Representation::Bits(_) => true,
            },
            TestCaseKind::Unsupported => false,
        }
    }
}

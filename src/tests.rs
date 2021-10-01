#![allow(warnings)]
use super::FpCategory;
use crate::consts::DecimalProps;
use crate::*;

#[test]
fn it_works() {
    //    //bid128_from_string 2 -9.9999999999999999999999999999999995 [afffed09bead87c0378d8e63ffffffff] 20
    //    use crate::d32;
    //    let expected = d32::from_bits(0x6018967f);
    //    let unpacked: crate::Unpacked<_> = expected.into();
    //    eprintln!("{:?}", unpacked);

    //    let expected = d128::from_bits(0x303a000000000000000000000000000b);
    //    eprintln!("{:?}", expected.unpack());

    //assert_eq!(Bits(.unwrap_or(d128::NAN).to_bits()), Bits(d128::from_bits(0x303a000000000000000000000000000b).to_bits()));
    let expected = d128::from_bits(0x303a000000000000000000000000000b);
    eprintln!("{:?}", expected.unpack());
    let actual = d128::parse_rounding("1.1e-2e", Rounding::Nearest).unwrap();
    eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());

    // let actual = d32::parse_rounding("25e-102", Rounding::Nearest).unwrap();
    // eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());
    //
    // let actual = d32::parse_rounding("251e-103", Rounding::Nearest).unwrap();
    // eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());

    //    let actual = d32::parse_rounding("9e-102", Rounding::Down).unwrap();
    //    eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());
    //    let actual = d32::parse_rounding("-9e-102", Rounding::Down).unwrap();
    //    eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());
    //    let actual = d32::parse_rounding("-4e-102", Rounding::Down).unwrap();
    //    eprintln!("{:x} => {:?} {}", actual.to_bits(), actual.unpack());

    //    let actual = d32::parse_rounding("9e-102", Rounding::Up).unwrap();
    //    eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());

    //    let actual = d32::parse_rounding("9e-102", Rounding::Zero).unwrap();
    //    eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());
    //
    //    let actual = d32::parse_rounding("9e-102", Rounding::TiesAway).unwrap();
    //    eprintln!("{:x} => {:?}", actual.to_bits(), actual.unpack());
}

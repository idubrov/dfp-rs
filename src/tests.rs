#![allow(warnings)]
use super::FpCategory;
use crate::consts::DecimalProps;
use crate::*;

type d32_down = Decimal<u32, DownRoundingContext>;

#[test]
fn it_works() {
    //assert_eq!(Bits(d32::<NearestRoundingContext>::from_bits(0x1f800000).add(d32::<NearestRoundingContext>::from_bits(0x9b800000)).to_bits()), Bits(d32::<NearestRoundingContext>::from_bits(0x1b800000).to_bits()));
    // let x: d32 = d32::from_bits(0x1f800000);
    // let y: d32 = d32::from_bits(0x9b800000);
    // let z: d32 = d32::from_bits(0x1b800000);
    // eprintln!("{:?} x", x.unpack());
    // eprintln!("{:?} y", y.unpack());
    // eprintln!("{:?} (x + y)", (x + y).unpack());
    // eprintln!("{:?} expected", z.unpack());
    //
    // //assert_eq!(Bits(Decimal::<u64, NearestRoundingContext>::parse_rounding("+234885.884424996e-295", Rounding::Nearest).unwrap().add(Decimal::<u64, NearestRoundingContext>::parse_rounding("+99.998989899989988e-287", Rounding::Nearest).unwrap()).to_bits()), Bits(Decimal::<u64, NearestRoundingContext>::from_bits(0x0c438d81c2bce2f6).to_bits()));
    // let x = Decimal::<u64, NearestRoundingContext>::parse_rounding("+234885.884424996e-295", Rounding::Nearest).unwrap();
    // let y = Decimal::<u64, NearestRoundingContext>::parse_rounding("+99.998989899989988e-287", Rounding::Nearest).unwrap();
    // let z = Decimal::<u64, NearestRoundingContext>::from_bits(0x0c438d81c2bce2f6);
    // eprintln!("{:?} x", x.unpack());
    // eprintln!("{:?} y", y.unpack());
    // eprintln!("{:?} (x + y)", (x + y).unpack());
    // eprintln!("{:?} expected", z.unpack());

    //assert_eq!(Bits(Decimal::<u64, DownRoundingContext>::from_bits(0x5ffffbfff34ffeb7).add(Decimal::<u64, DownRoundingContext>::from_bits(0x5ffffff5efffef7f)).to_bits()), Bits(Decimal::<u64, DownRoundingContext>::from_bits(0x77fb86f26fc0ffff).to_bits()));
    //let x = Decimal::<u64, DownRoundingContext>::parse_rounding("-1110100.00110000101e267", Rounding::Nearest).unwrap();
    //let y = Decimal::<u64, DownRoundingContext>::parse_rounding("+1001.00e-249", Rounding::Nearest).unwrap();
    // let x = Decimal::<u64, DownRoundingContext>::from_bits(0x5ffffbfff34ffeb7);
    // let y = Decimal::<u64, DownRoundingContext>::from_bits(0x5ffffff5efffef7f);
    // let z = Decimal::<u64, DownRoundingContext>::from_bits(0x77fb86f26fc0ffff);
    //
    // eprintln!("{:?} x", x.unpack());
    // eprintln!("{:?} y", y.unpack());
    // //eprintln!("{:?} (x + y)", (x + y).unpack());
    // eprintln!("{:?} expected", z.unpack());

    // let y: d128 = "+5695567.598669978987e6134".parse().unwrap();
    // // should be: 12298
    // eprintln!("{:?}", y.unpack());
}

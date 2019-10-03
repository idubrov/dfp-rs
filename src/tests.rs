use super::FpCategory;
use crate::consts::DecimalProps;
use crate::{d32, Decimal, Rounding, Unpacked};

#[test]
fn it_works() {
    //    //bid128_from_string 2 -9.9999999999999999999999999999999995 [afffed09bead87c0378d8e63ffffffff] 20
    //    use crate::d32;
    //    let expected = d32::from_bits(0x6018967f);
    //    let unpacked: crate::Unpacked<_> = expected.into();
    //    eprintln!("{:?}", unpacked);
    let actual = d32::parse_rounding("+Inf", Rounding::Nearest).unwrap();
    eprintln!("{:?}", actual.unpack());
}

use super::FpCategory;
use crate::consts::DecimalProps;
use crate::{d32, Decimal, Rounding, Unpacked};

#[test]
fn it_works() {
    //bid128_from_string 2 -9.9999999999999999999999999999999995 [afffed09bead87c0378d8e63ffffffff] 20
    use crate::d128;
    let expected = d128::from_bits(0xafffed09bead87c0378d8e63ffffffff);
    let unpacked: crate::Unpacked<_> = expected.into();
    eprintln!("{:?}", unpacked);
    let actual =
        d128::parse_rounding("-9.9999999999999999999999999999999995", Rounding::Up).unwrap();
    eprintln!("{:?}", actual.unpack());
}

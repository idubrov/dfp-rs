//! Rust bindings for Intel(R) Decimal Floating-Point Math Library
#![allow(warnings)]

extern crate dfp_sys;

#[derive(Clone, Copy)]
pub struct DecFloat32(dfp_sys::BID_UINT32);
#[derive(Clone, Copy)]
pub struct DecFloat64(dfp_sys::BID_UINT64);
#[derive(Clone, Copy)]
pub struct DecFloat128(dfp_sys::BID_UINT128);

const DEFAULT_ROUNDING: u32 = dfp_sys::BID_ROUNDING_TO_NEAREST;

use std::ffi::{CString, CStr};
use std::{fmt, str};

use std::ops::{Add, Sub, AddAssign, SubAssign, Mul, MulAssign, Div, DivAssign};

#[derive(Debug)]
pub enum Error {
    Invalid,
    Denormal,
    ZeroDivide,
    Overflow,
    Underflow,
    Inexact,

    // FIXME: remove once custom parsing is implemented
    InvalidString,
}


/// Check DFP library flags and raise a corresponding error
fn check_flags(flags: dfp_sys::_IDEC_flags) -> Result<(), Error> {
    if (flags & dfp_sys::BID_INVALID_EXCEPTION) != 0 {
        Err(Error::Invalid)
    } else if (flags & dfp_sys::BID_DENORMAL_EXCEPTION) != 0 {
        Err(Error::Denormal)
    } else if (flags & dfp_sys::BID_ZERO_DIVIDE_EXCEPTION) != 0 {
        Err(Error::ZeroDivide)
    } else if (flags & dfp_sys::BID_OVERFLOW_EXCEPTION) != 0 {
        Err(Error::Overflow)
    } else if (flags & dfp_sys::BID_UNDERFLOW_EXCEPTION) != 0 {
        Err(Error::Underflow)
    } else if flags == 0 || flags == dfp_sys::BID_INEXACT_EXCEPTION {
        Ok(())
    } else {
        unreachable!()
    }
}

impl str::FromStr for DecFloat128 {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Error> {
        unsafe {
            let cstr = CString::new(s).map_err(|_| Error::InvalidString)?;
            let raw = cstr.into_raw();
            let mut flags = 0;
            let res = dfp_sys::__bid128_from_string(raw, 0, &mut flags);
            let _ = CString::from_raw(raw);

            check_flags(flags)?;
            Ok(DecFloat128(res))
        }
    }
}

macro_rules! op_assign_impl {
    ($op:ident $opf:ident $t:ident $f:ident) => (
        impl $op for $t {
            fn $opf(&mut self, other: $t) {
                unsafe {
                    let mut flags = 0;
                    let result = dfp_sys::$f(self.0, other.0, 0, &mut flags);
                    check_flags(flags).unwrap();
                    self.0 = result;
                }
            }
        }
    )
}

macro_rules! op_impl {
    ($op:ident $opf:ident $t:ident $f:ident) => (
        impl $op for $t {
            type Output = $t;

            fn $opf(self, other: $t) -> $t {
                unsafe {
                    let mut flags = 0;
                    let result = dfp_sys::$f(self.0, other.0, DEFAULT_ROUNDING, &mut flags);
                    check_flags(flags).unwrap();
                    $t(result)
                }
            }
        }
    )
}

// DecFloat32
op_assign_impl!(AddAssign add_assign DecFloat32 __bid32_add);
op_assign_impl!(SubAssign sub_assign DecFloat32 __bid32_sub);
op_assign_impl!(MulAssign mul_assign DecFloat32 __bid32_mul);
op_assign_impl!(DivAssign div_assign DecFloat32 __bid32_div);

op_impl!(Add add DecFloat32 __bid32_add);
op_impl!(Sub sub DecFloat32 __bid32_add);
op_impl!(Mul mul DecFloat32 __bid32_mul);
op_impl!(Div div DecFloat32 __bid32_div);

// DecFloat64
op_assign_impl!(AddAssign add_assign DecFloat64 __bid64_add);
op_assign_impl!(SubAssign sub_assign DecFloat64 __bid64_sub);
op_assign_impl!(MulAssign mul_assign DecFloat64 __bid64_mul);
op_assign_impl!(DivAssign div_assign DecFloat64 __bid64_div);

op_impl!(Add add DecFloat64 __bid64_add);
op_impl!(Sub sub DecFloat64 __bid64_add);
op_impl!(Mul mul DecFloat64 __bid64_mul);
op_impl!(Div div DecFloat64 __bid64_div);

// DecFloat128
op_assign_impl!(AddAssign add_assign DecFloat128 __bid128_add);
op_assign_impl!(SubAssign sub_assign DecFloat128 __bid128_sub);
op_assign_impl!(MulAssign mul_assign DecFloat128 __bid128_mul);
op_assign_impl!(DivAssign div_assign DecFloat128 __bid128_div);

op_impl!(Add add DecFloat128 __bid128_add);
op_impl!(Sub sub DecFloat128 __bid128_add);
op_impl!(Mul mul DecFloat128 __bid128_mul);
op_impl!(Div div DecFloat128 __bid128_div);

impl fmt::Display for DecFloat128 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe {
            // Maximum buffer size?
            let mut buf: [i8; 64] = std::mem::uninitialized();
            let mut flags = 0;
            dfp_sys::__bid128_to_string(buf.as_mut_ptr(), self.0, &mut flags);
            let cstr = CStr::from_ptr(buf.as_ptr());
            cstr.to_string_lossy().fmt(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_test() {
        let x = "123.3".parse::<DecFloat128>().unwrap();
        let y = "456.4".parse::<DecFloat128>().unwrap();
        let z = x + y;
        assert_eq!("+5797E-1", z.to_string());
    }

    #[test]
    fn add_assign_test() {
        let mut x = "123.3".parse::<DecFloat128>().unwrap();
        let y = "456.4".parse::<DecFloat128>().unwrap();
        x += y;
        assert_eq!("+5797E-1", x.to_string());
    }
}
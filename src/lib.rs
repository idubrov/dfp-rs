//! Rust bindings for Intel(R) Decimal Floating-Point Math Library
#![allow(warnings)]

mod bindings;

#[derive(Clone, Copy, Debug)]
pub struct DecFloat32(bindings::BID_UINT32);
#[derive(Clone, Copy, Debug)]
pub struct DecFloat64(bindings::BID_UINT64);
#[derive(Clone, Copy, Debug)]
pub struct DecFloat128(bindings::BID_UINT128);

const DEFAULT_ROUNDING: u32 = bindings::BID_ROUNDING_TO_NEAREST;

use std::ffi::{CStr, CString};
use std::{fmt, str};

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

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

macro_rules! binary_func {
    ($t:ident $name:ident $f:ident) => (
        pub fn $name(self, other: &Self) -> Self {
            unsafe {
                let mut flags = 0;
                let res = bindings::$f(self.0, other.0, DEFAULT_ROUNDING, &mut flags);
                check_flags(flags).unwrap();
                $t(res)
            }
        }
    )
}

impl DecFloat32 {
    binary_func!(DecFloat32 pow __bid32_pow);

    pub fn one() -> Self {
        DecFloat32::from_bits(0b1100101 << (32 - 9) | 1)
    }

    pub fn to_bits(self) -> u32 {
        self.0
    }

    pub fn from_bits(v: u32) -> DecFloat32 {
        DecFloat32(v)
    }
}

impl DecFloat64 {
    binary_func!(DecFloat64 pow __bid64_pow);

    pub fn one() -> Self {
        DecFloat64::from_bits(0b110001110 << (64 - 11) | 1)
    }

    pub fn from_bits(v: u64) -> DecFloat64 {
        DecFloat64(v)
    }

    pub fn to_bits(self) -> u64 {
        self.0
    }
}

impl DecFloat128 {
    binary_func!(DecFloat128 pow __bid128_pow);

    pub fn one() -> Self {
        DecFloat128::from_bits(0b1100000100000 << (128 - 15) | 1)
    }

    pub fn from_bits(v: u128) -> Self {
        unsafe { DecFloat128(std::mem::transmute(v)) }
    }

    pub fn to_bits(self) -> u128 {
        unsafe { std::mem::transmute(self) }
    }
}

macro_rules! partial_eq_impl {
    ($t:ident $f:ident) => {
        impl PartialEq for $t {
            fn eq(&self, other: &Self) -> bool {
                unsafe {
                    let mut flags = 0;
                    let res = bindings::$f(self.0, other.0, &mut flags);
                    check_flags(flags).unwrap();
                    res != 0
                }
            }
        }
    };
}

partial_eq_impl!(DecFloat32 __bid32_quiet_equal);
partial_eq_impl!(DecFloat64 __bid64_quiet_equal);
partial_eq_impl!(DecFloat128 __bid128_quiet_equal);

// From implementations
macro_rules! from_impl {
    ($s:ident $t:ident $f:ident) => {
        impl From<$s> for $t {
            fn from(value: $s) -> $t {
                unsafe { $t(bindings::$f(value)) }
            }
        }
    };
}

// These four are fallible, so not provided (until we have TryFrom)
//from_impl!(i32 DecFloat32 __bid32_from_int32);
//from_impl!(u32 DecFloat32 __bid32_from_uint32);
//from_impl!(i64 DecFloat32 __bid32_from_int64);
//from_impl!(u64 DecFloat32 __bid32_from_uint64);

from_impl!(i32 DecFloat64 __bid64_from_int32);
from_impl!(u32 DecFloat64 __bid64_from_uint32);
// These two are fallible, so not provided (until we have TryFrom)
//from_impl!(i64 DecFloat64 __bid64_from_int64);
//from_impl!(u64 DecFloat64 __bid64_from_uint64);

from_impl!(i32 DecFloat128 __bid128_from_int32);
from_impl!(u32 DecFloat128 __bid128_from_uint32);
from_impl!(i64 DecFloat128 __bid128_from_int64);
from_impl!(u64 DecFloat128 __bid128_from_uint64);

// Operations
macro_rules! op_assign_impl {
    ($op:ident $opf:ident $t:ident $f:ident) => {
        impl $op for $t {
            fn $opf(&mut self, other: $t) {
                unsafe {
                    let mut flags = 0;
                    let result = bindings::$f(self.0, other.0, DEFAULT_ROUNDING, &mut flags);
                    check_flags(flags).unwrap();
                    self.0 = result;
                }
            }
        }
    };
}

macro_rules! op_impl {
    ($op:ident $opf:ident $t:ident $f:ident) => {
        impl $op for $t {
            type Output = $t;

            fn $opf(self, other: $t) -> $t {
                unsafe {
                    let mut flags = 0;
                    let result = bindings::$f(self.0, other.0, DEFAULT_ROUNDING, &mut flags);
                    check_flags(flags).unwrap();
                    $t(result)
                }
            }
        }
    };
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

/// Check DFP library flags and raise a corresponding error
fn check_flags(flags: bindings::_IDEC_flags) -> Result<(), Error> {
    if (flags & bindings::BID_INVALID_EXCEPTION) != 0 {
        Err(Error::Invalid)
    } else if (flags & bindings::BID_DENORMAL_EXCEPTION) != 0 {
        Err(Error::Denormal)
    } else if (flags & bindings::BID_ZERO_DIVIDE_EXCEPTION) != 0 {
        Err(Error::ZeroDivide)
    } else if (flags & bindings::BID_OVERFLOW_EXCEPTION) != 0 {
        Err(Error::Overflow)
    } else if (flags & bindings::BID_UNDERFLOW_EXCEPTION) != 0 {
        Err(Error::Underflow)
    } else if flags == 0 || flags == bindings::BID_INEXACT_EXCEPTION {
        Ok(())
    } else {
        unreachable!()
    }
}

// Temporary string conversions

macro_rules! str_conv_impl {
    ($t:ident $from:ident $to:ident) => {
        impl str::FromStr for $t {
            type Err = Error;

            fn from_str(s: &str) -> Result<Self, Error> {
                unsafe {
                    let cstr = CString::new(s).map_err(|_| Error::InvalidString)?;
                    let raw = cstr.into_raw();
                    let mut flags = 0;
                    let res = bindings::$from(raw, 0, &mut flags);
                    let _ = CString::from_raw(raw);

                    check_flags(flags)?;
                    Ok($t(res))
                }
            }
        }

        impl fmt::Display for $t {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                unsafe {
                    // Maximum buffer size?
                    let mut buf: [i8; 64] = std::mem::uninitialized();
                    let mut flags = 0;
                    bindings::$to(buf.as_mut_ptr(), self.0, &mut flags);
                    let cstr = CStr::from_ptr(buf.as_ptr());
                    cstr.to_string_lossy().fmt(f)
                }
            }
        }
    };
}

str_conv_impl!(DecFloat32 __bid32_from_string __bid32_to_string);
str_conv_impl!(DecFloat64 __bid64_from_string __bid64_to_string);
str_conv_impl!(DecFloat128 __bid128_from_string __bid128_to_string);

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

    #[test]
    fn pow_test() {
        let x: DecFloat128 = 10i64.into();
        let x = x.pow(&10i64.into());
        assert_eq!("+10000000000E+0", x.to_string());
    }

    #[test]
    fn one() {
        assert_eq!(DecFloat32::one(), "1".parse().unwrap());
        assert_eq!(DecFloat64::one(), "1".parse().unwrap());
        assert_eq!(DecFloat128::one(), "1".parse().unwrap());
    }
}

//! Rust bindings for Intel(R) Decimal Floating-Point Math Library
#![allow(non_camel_case_types)]

use std::cell::Cell;
use std::ffi::{CStr, CString};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::{fmt, str};

#[allow(non_snake_case)]
#[allow(non_upper_case_globals)]
#[allow(dead_code)]
mod details {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    #[test]
    fn sanity_test() {
        unsafe {
            let x = __bid128_from_uint64(123);
            let y = __bid128_from_uint64(789);

            let mut flags: _IDEC_flags = 0;
            let z = __bid128_add(x, y, 0, &mut flags);
            assert_eq!(0, flags);
            let r = __bid128_to_uint64_int(z, &mut flags);
            assert_eq!(0, flags);
            assert_eq!(912, r)
        }
    }
}

use details::_IDEC_round;

#[derive(Clone, Copy, Default, Debug)]
pub struct Flags(details::_IDEC_flags);

impl Flags {
    pub fn is_invalid(&self) -> bool {
        (self.0 & details::BID_INVALID_EXCEPTION) != 0
    }

    pub fn is_denormal(&self) -> bool {
        (self.0 & details::BID_DENORMAL_EXCEPTION) != 0
    }

    pub fn is_zero_divide(&self) -> bool {
        (self.0 & details::BID_ZERO_DIVIDE_EXCEPTION) != 0
    }

    pub fn is_overflow(&self) -> bool {
        (self.0 & details::BID_OVERFLOW_EXCEPTION) != 0
    }

    pub fn is_underflow(&self) -> bool {
        (self.0 & details::BID_UNDERFLOW_EXCEPTION) != 0
    }

    pub fn is_inexact(&self) -> bool {
        (self.0 & details::BID_INEXACT_EXCEPTION) != 0
    }

    pub fn is_clear(&self) -> bool {
        self.0 == 0
    }
}

#[repr(u32)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rounding {
    Nearest = 0,
    Down = 1,
    Up = 2,
    Zero = 3,
    TiesAway = 4,
}

impl Default for Rounding {
    fn default() -> Self {
        Rounding::Nearest
    }
}

pub trait Context {
    fn op<T, F: FnOnce(Rounding) -> (T, Flags)>(cb: F) -> T;
}

/// A default implementation of context which always uses `Nearest` rounding and ignores exceptions
/// set by the floating point library.
pub struct DefaultContext;

impl Context for DefaultContext {
    fn op<T, F: FnOnce(Rounding) -> (T, Flags)>(cb: F) -> T {
        let (res, _flags) = cb(Default::default());
        res
    }
}

#[derive(Clone, Copy, Default)]
struct ContextInner {
    flags: Flags,
    round: Rounding,
}

impl ContextInner {
    fn new(flags: Flags, round: Rounding) -> Self {
        Self { flags, round }
    }
}

thread_local!(static CONTEXT: Cell<ContextInner> = Cell::new(Default::default()));

/// A `Context` implementation which uses thread local to keep the rounding mode and flags of the
/// last operation.
pub struct CheckedContext;

impl Context for CheckedContext {
    fn op<T, F: FnOnce(Rounding) -> (T, Flags)>(cb: F) -> T {
        CONTEXT.with(|ctx| {
            let round = ctx.get().round;
            let (res, flags) = cb(round);
            ctx.set(ContextInner::new(flags, round));
            res
        })
    }
}

impl CheckedContext {
    pub fn reset_flags() {
        CONTEXT.with(|ctx| ctx.set(ContextInner::new(Flags(0), ctx.get().round)))
    }

    pub fn get_flags() -> Flags {
        CONTEXT.with(|ctx| ctx.get().flags)
    }

    pub fn set_rounding(round: Rounding) {
        CONTEXT.with(|ctx| ctx.set(ContextInner::new(ctx.get().flags, round)))
    }

    pub fn get_rounding() -> Rounding {
        CONTEXT.with(|ctx| ctx.get().round)
    }
}

/// A 32-bit decimal floating point type, as specified by IEEE 754-2008.
pub struct d32<T = DefaultContext>(details::BID_UINT32, PhantomData<*const T>)
where
    T: Context;

/// A 64-bit decimal floating point type, as specified by IEEE 754-2008.
pub struct d64<T = DefaultContext>(details::BID_UINT64, PhantomData<*const T>)
where
    T: Context;

/// A 128-bit decimal floating point type, as specified by IEEE 754-2008.
pub struct d128<T = DefaultContext>(details::BID_UINT128, PhantomData<*const T>)
where
    T: Context;

// Have to implement `Clone` ourselves: https://github.com/rust-lang/rust/issues/26925

impl<T: Context> Clone for d32<T> {
    fn clone(&self) -> Self {
        d32::new(self.0)
    }
}
impl<T: Context> Copy for d32<T> {}

impl<T: Context> Clone for d64<T> {
    fn clone(&self) -> Self {
        d64::new(self.0)
    }
}
impl<T: Context> Copy for d64<T> {}

impl<T: Context> Clone for d128<T> {
    fn clone(&self) -> Self {
        d128::new(self.0)
    }
}
impl<T: Context> Copy for d128<T> {}

#[derive(Debug)]
pub enum Error {
    InvalidString,
}

macro_rules! binary_func {
    ($t:ident $name:ident $f:ident) => (
        pub fn $name(self, other: &Self) -> Self {
            T::op(|round| unsafe {
                let mut flags = 0;
                let res = $t::new(details::$f(self.0, other.0, round as _IDEC_round, &mut flags));
                (res, Flags(flags))
            })
        }
    )
}

macro_rules! str_conv_impl {
    ($t:ident $from:ident $to:ident) => {
        impl<T: Context> str::FromStr for $t<T> {
            type Err = Error;

            fn from_str(s: &str) -> Result<Self, Error> {
                T::op(|round| unsafe {
                    let cstr = CString::new(s).map_err(|_| Error::InvalidString);
                    match cstr {
                        Ok(cstr) => {
                            let raw = cstr.into_raw();
                            let mut flags = 0;
                            let res = details::$from(raw, round as _IDEC_round, &mut flags);
                            let _ = CString::from_raw(raw);
                            let res = Ok($t::new(res));
                            (res, Flags(flags))
                        }
                        Err(e) => (Err(e), Flags(0)),
                    }
                })
            }
        }

        impl<T: Context> fmt::Display for $t<T> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                T::op(|_round| unsafe {
                    // Maximum buffer size?
                    let mut buf: [i8; 64] = std::mem::uninitialized();
                    let mut flags = 0;
                    details::$to(buf.as_mut_ptr(), self.0, &mut flags);
                    let cstr = CStr::from_ptr(buf.as_ptr());
                    let res = cstr.to_string_lossy().fmt(f);
                    (res, Flags(flags))
                })
            }
        }

        impl<T: Context> fmt::Debug for $t<T> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{:x}", self.to_bits())
            }
        }
    };
}

macro_rules! partial_eq_impl {
    ($t:ident $f:ident) => {
        impl<T: Context> PartialEq for $t<T> {
            fn eq(&self, other: &Self) -> bool {
                T::op(|_round| unsafe {
                    let mut flags = 0;
                    let res = details::$f(self.0, other.0, &mut flags);
                    (res != 0, Flags(flags))
                })
            }
        }
    };
}

macro_rules! from_impl {
    ($s:ident $t:ident $f:ident) => {
        impl<T: Context> From<$s> for $t<T> {
            fn from(value: $s) -> Self {
                unsafe { $t::new(details::$f(value)) }
            }
        }
    };
}

macro_rules! from_checked_impl {
    ($s:ident $t:ident $f:ident) => {
        impl<T: Context> From<$s> for $t<T> {
            fn from(value: $s) -> Self {
                T::op(|round| unsafe {
                    let mut flags = 0;
                    let res = $t::new(details::$f(value, round as _IDEC_round, &mut flags));
                    (res, Flags(flags))
                })
            }
        }
    };
}

// Operations
macro_rules! op_assign_impl {
    ($op:ident $opf:ident $t:ident $f:ident) => {
        impl<T: Context> $op for $t<T> {
            fn $opf(&mut self, other: $t<T>) {
                T::op(|round| unsafe {
                    let mut flags = 0;
                    self.0 = details::$f(self.0, other.0, round as _IDEC_round, &mut flags);
                    ((), Flags(flags))
                })
            }
        }
    };
}

macro_rules! op_impl {
    ($op:ident $opf:ident $t:ident $f:ident) => {
        impl<T: Context> $op for $t<T> {
            type Output = $t;

            fn $opf(self, other: $t<T>) -> $t {
                T::op(|round| unsafe {
                    let mut flags = 0;
                    let res = $t::new(details::$f(
                        self.0,
                        other.0,
                        round as _IDEC_round,
                        &mut flags,
                    ));
                    (res, Flags(flags))
                })
            }
        }
    };
}

impl<T: Context> d32<T> {
    fn new(v: details::BID_UINT32) -> Self {
        d32(v, PhantomData)
    }

    binary_func!(d32 pow __bid32_pow);

    pub fn to_bits(self) -> u32 {
        self.0
    }
}

impl d32 {
    pub fn one() -> Self {
        d32::from_bits(0b1100101 << (32 - 9) | 1)
    }

    pub fn from_bits(v: u32) -> Self {
        d32::new(v)
    }

    pub fn as_checked(self) -> d32<CheckedContext> {
        d32::new(self.0)
    }
}

impl<T: Context> d64<T> {
    fn new(v: details::BID_UINT64) -> Self {
        d64(v, PhantomData)
    }

    binary_func!(d64 pow __bid64_pow);

    pub fn to_bits(self) -> u64 {
        self.0
    }
}

impl d64 {
    pub fn one() -> Self {
        d64::from_bits(0b110001110 << (64 - 11) | 1)
    }

    pub fn from_bits(v: u64) -> Self {
        d64::new(v)
    }

    pub fn as_checked(self) -> d64<CheckedContext> {
        d64::new(self.0)
    }
}

impl<T: Context> d128<T> {
    fn new(v: details::BID_UINT128) -> Self {
        d128(v, PhantomData)
    }

    binary_func!(d128 pow __bid128_pow);

    pub fn to_bits(self) -> u128 {
        unsafe { std::mem::transmute(self) }
    }
}

impl d128 {
    pub fn one() -> Self {
        d128::from_bits(0b1100000100000 << (128 - 15) | 1)
    }

    pub fn from_bits(v: u128) -> Self {
        unsafe { d128::new(std::mem::transmute(v)) }
    }

    pub fn as_checked(self) -> d128<CheckedContext> {
        d128::new(self.0)
    }
}

partial_eq_impl!(d32 __bid32_quiet_equal);
partial_eq_impl!(d64 __bid64_quiet_equal);
partial_eq_impl!(d128 __bid128_quiet_equal);

from_checked_impl!(i32 d32 __bid32_from_int32);
from_checked_impl!(u32 d32 __bid32_from_uint32);
from_checked_impl!(i64 d32 __bid32_from_int64);
from_checked_impl!(u64 d32 __bid32_from_uint64);

from_impl!(i32 d64 __bid64_from_int32);
from_impl!(u32 d64 __bid64_from_uint32);
from_checked_impl!(i64 d64 __bid64_from_int64);
from_checked_impl!(u64 d64 __bid64_from_uint64);

from_impl!(i32 d128 __bid128_from_int32);
from_impl!(u32 d128 __bid128_from_uint32);
from_impl!(i64 d128 __bid128_from_int64);
from_impl!(u64 d128 __bid128_from_uint64);

// d32
op_assign_impl!(AddAssign add_assign d32 __bid32_add);
op_assign_impl!(SubAssign sub_assign d32 __bid32_sub);
op_assign_impl!(MulAssign mul_assign d32 __bid32_mul);
op_assign_impl!(DivAssign div_assign d32 __bid32_div);

op_impl!(Add add d32 __bid32_add);
op_impl!(Sub sub d32 __bid32_add);
op_impl!(Mul mul d32 __bid32_mul);
op_impl!(Div div d32 __bid32_div);

// d64
op_assign_impl!(AddAssign add_assign d64 __bid64_add);
op_assign_impl!(SubAssign sub_assign d64 __bid64_sub);
op_assign_impl!(MulAssign mul_assign d64 __bid64_mul);
op_assign_impl!(DivAssign div_assign d64 __bid64_div);

op_impl!(Add add d64 __bid64_add);
op_impl!(Sub sub d64 __bid64_add);
op_impl!(Mul mul d64 __bid64_mul);
op_impl!(Div div d64 __bid64_div);

// d128
op_assign_impl!(AddAssign add_assign d128 __bid128_add);
op_assign_impl!(SubAssign sub_assign d128 __bid128_sub);
op_assign_impl!(MulAssign mul_assign d128 __bid128_mul);
op_assign_impl!(DivAssign div_assign d128 __bid128_div);

op_impl!(Add add d128 __bid128_add);
op_impl!(Sub sub d128 __bid128_add);
op_impl!(Mul mul d128 __bid128_mul);
op_impl!(Div div d128 __bid128_div);

str_conv_impl!(d32 __bid32_from_string __bid32_to_string);
str_conv_impl!(d64 __bid64_from_string __bid64_to_string);
str_conv_impl!(d128 __bid128_from_string __bid128_to_string);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_test() {
        let x = "123.3".parse::<d128>().unwrap();
        let y = "456.4".parse::<d128>().unwrap();
        let z = x + y;
        assert_eq!("+5797E-1", z.to_string());
    }

    #[test]
    fn add_assign_test() {
        let mut x = "123.3".parse::<d128>().unwrap();
        let y = "456.4".parse::<d128>().unwrap();
        x += y;
        assert_eq!("+5797E-1", x.to_string());
    }

    #[test]
    fn pow_test() {
        let x: d128 = 10i64.into();
        let x = x.pow(&10i64.into());
        assert_eq!("+10000000000E+0", x.to_string());
    }

    #[test]
    fn one() {
        assert_eq!(d32::one(), "1".parse().unwrap());
        assert_eq!(d64::one(), "1".parse().unwrap());
        assert_eq!(d128::one(), "1".parse().unwrap());
    }

    #[test]
    fn flags_raised() {
        let x: d128 = 1.into();
        let y: d128 = 0.into();

        // Context is not updated by default
        assert!(CheckedContext::get_flags().is_clear());
        let _z = x / y;
        assert!(CheckedContext::get_flags().is_clear());

        // With checked values, context is updated
        let x = x.as_checked();
        let y = y.as_checked();
        assert!(CheckedContext::get_flags().is_clear());
        let _z = x / y;
        assert!(CheckedContext::get_flags().is_zero_divide());
        assert!(!CheckedContext::get_flags().is_clear());
    }

    #[test]
    fn failing_conversions() {
        let _x: d32 = 0xffff_ffffu32.into();
        assert!(CheckedContext::get_flags().is_clear());

        let _x: d32<CheckedContext> = 0xffff_ffffu32.into();
        assert!(!CheckedContext::get_flags().is_clear());
        assert!(CheckedContext::get_flags().is_inexact());
    }
}

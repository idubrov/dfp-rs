#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[cfg(test)]
mod tests {
    use super::*;

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

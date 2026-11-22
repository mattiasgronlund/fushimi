// The tests' `next_up` and `next_down` of `f64`, which return what `f64::next_up` and
// `f64::next_down` return. The standard library has those only from Rust 1.86, and the tests
// compile on the MSRV, 1.85. The bodies are those of the standard library: the bit patterns of
// the non-NaN `f64`s of one sign are ordered as their magnitudes, so each step from a nonzero
// `f64` adds 1 to its bits or subtracts 1 from them.

/// `next_up(x)` is the least `f64` greater than `x`: `x` itself if `x` is NaN or +∞, and
/// 2^-1074 if `x` is ±0, as `f64::next_up`.
pub(crate) const fn next_up(x: f64) -> f64 {
    let bits = x.to_bits();
    if x.is_nan() || bits == f64::INFINITY.to_bits() {
        return x;
    }
    let abs = bits & !(1 << 63);
    let next = if abs == 0 {
        // The least positive subnormal, 2^-1074.
        1
    } else if bits == abs {
        bits + 1
    } else {
        bits - 1
    };
    f64::from_bits(next)
}

/// `next_down(x)` is the greatest `f64` less than `x`: `x` itself if `x` is NaN or -∞, and
/// -2^-1074 if `x` is ±0, as `f64::next_down`.
pub(crate) const fn next_down(x: f64) -> f64 {
    let bits = x.to_bits();
    if x.is_nan() || bits == f64::NEG_INFINITY.to_bits() {
        return x;
    }
    let abs = bits & !(1 << 63);
    let next = if abs == 0 {
        // The greatest negative subnormal, -2^-1074.
        0x8000_0000_0000_0001
    } else if bits == abs {
        bits - 1
    } else {
        bits + 1
    };
    f64::from_bits(next)
}

// Each case is (the bits of x, the bits of the result), with the results of `f64::next_up` and
// `f64::next_down` written out by hand: NaNs, the zeros, the infinities, the subnormals and
// their boundary with the normal numbers, ±1 and ±MAX.
#[test]
fn next_up_cases() {
    let cases = [
        (0x7ff8_0000_0000_0000, 0x7ff8_0000_0000_0000), // NaN
        (0xfff8_0000_0000_0001, 0xfff8_0000_0000_0001), // a negative NaN with a payload
        (0x7ff0_0000_0000_0000, 0x7ff0_0000_0000_0000), // +∞
        (0xfff0_0000_0000_0000, 0xffef_ffff_ffff_ffff), // -∞ to -MAX
        (0x0000_0000_0000_0000, 0x0000_0000_0000_0001), // +0 to 2^-1074
        (0x8000_0000_0000_0000, 0x0000_0000_0000_0001), // -0 to 2^-1074
        (0x0000_0000_0000_0001, 0x0000_0000_0000_0002), // 2^-1074
        (0x000f_ffff_ffff_ffff, 0x0010_0000_0000_0000), // the greatest subnormal to MIN_POSITIVE
        (0x8000_0000_0000_0001, 0x8000_0000_0000_0000), // -2^-1074 to -0
        (0x8010_0000_0000_0000, 0x800f_ffff_ffff_ffff), // -MIN_POSITIVE
        (0x3ff0_0000_0000_0000, 0x3ff0_0000_0000_0001), // 1
        (0xbff0_0000_0000_0000, 0xbfef_ffff_ffff_ffff), // -1
        (0x7fef_ffff_ffff_ffff, 0x7ff0_0000_0000_0000), // MAX to +∞
        (0xffef_ffff_ffff_ffff, 0xffef_ffff_ffff_fffe), // -MAX
    ];
    for (x, want) in cases {
        let got = next_up(f64::from_bits(x)).to_bits();
        assert_eq!(
            got, want,
            "next_up({x:#018x}) = {got:#018x}, not {want:#018x}"
        );
    }
}

#[test]
fn next_down_cases() {
    let cases = [
        (0x7ff8_0000_0000_0000, 0x7ff8_0000_0000_0000), // NaN
        (0xfff8_0000_0000_0001, 0xfff8_0000_0000_0001), // a negative NaN with a payload
        (0xfff0_0000_0000_0000, 0xfff0_0000_0000_0000), // -∞
        (0x7ff0_0000_0000_0000, 0x7fef_ffff_ffff_ffff), // +∞ to MAX
        (0x0000_0000_0000_0000, 0x8000_0000_0000_0001), // +0 to -2^-1074
        (0x8000_0000_0000_0000, 0x8000_0000_0000_0001), // -0 to -2^-1074
        (0x8000_0000_0000_0001, 0x8000_0000_0000_0002), // -2^-1074
        (0x800f_ffff_ffff_ffff, 0x8010_0000_0000_0000), // the least subnormal to -MIN_POSITIVE
        (0x0000_0000_0000_0001, 0x0000_0000_0000_0000), // 2^-1074 to +0
        (0x0010_0000_0000_0000, 0x000f_ffff_ffff_ffff), // MIN_POSITIVE
        (0x3ff0_0000_0000_0000, 0x3fef_ffff_ffff_ffff), // 1
        (0xbff0_0000_0000_0000, 0xbff0_0000_0000_0001), // -1
        (0xffef_ffff_ffff_ffff, 0xfff0_0000_0000_0000), // -MAX to -∞
        (0x7fef_ffff_ffff_ffff, 0x7fef_ffff_ffff_fffe), // MAX
    ];
    for (x, want) in cases {
        let got = next_down(f64::from_bits(x)).to_bits();
        assert_eq!(
            got, want,
            "next_down({x:#018x}) = {got:#018x}, not {want:#018x}"
        );
    }
}

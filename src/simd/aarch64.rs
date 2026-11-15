use std::{arch::aarch64::*, mem::transmute};

pub(crate) const HAS_MAXIMUM: bool = true;

pub(crate) type F64X2 = float64x2_t;

pub(crate) fn abs(x: F64X2) -> F64X2 {
    unsafe { vabsq_f64(x) }
}

// Inlined, as the crate's operations inline it, where `mul_add_ru` or `sqrt_rd_ru` calls it
// (see `aarch64/fma.rs`). Those two are `#[inline(always)]` (see `Baseline` in
// `src/simd/token.rs`), so without this, a `*_with` method instantiated in another crate calls
// it out of line. The same holds for `all`, `and`, `eq`, `gt`, `lt`, `or` and `sub_rn`.
#[inline(always)]
pub(crate) fn add_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vaddq_f64(x, y) }
}

// Inlined, as `add_rn` is.
#[inline(always)]
pub(crate) fn all(x: F64X2) -> bool {
    unsafe { transmute::<uint32x2_t, u64>(vmovn_u64(transmute::<F64X2, uint64x2_t>(x))) == !0u64 }
}

// Inlined, as `add_rn` is.
#[inline(always)]
pub(crate) fn and(x: F64X2, y: F64X2) -> F64X2 {
    unsafe {
        transmute(vandq_u64(
            transmute::<F64X2, uint64x2_t>(x),
            transmute::<F64X2, uint64x2_t>(y),
        ))
    }
}

pub(crate) fn any(x: F64X2) -> bool {
    unsafe { transmute::<uint32x2_t, u64>(vmovn_u64(transmute::<F64X2, uint64x2_t>(x))) != 0u64 }
}

/// `bitmask([x0, x1]) = b0 | b1 << 1`, where bi is 1 if xi has all bits set and 0 if it
/// has none. Each xi must be one or the other, as the comparisons return.
// Inlined, as `ge` is.
#[inline(always)]
pub(crate) fn bitmask(x: F64X2) -> u32 {
    // `vmovn_u64` keeps the low 32 bits of each lane, so n = x1[31:0] << 32 | x0[31:0] on
    // little-endian targets. Bit 31 of n is a bit of x0 and bit 32 a bit of x1. Reading
    // both lanes as `u64`s instead, LLVM took 29 instructions in `Interval::mul` (apple-m1)
    // to turn the four comparisons of `classify2` into its class. This takes 17, or 18 with
    // 16 codegen units: an `xtn` and an `fmov` per comparison, then shifts, masks and `orr`s.
    let n = unsafe { transmute::<uint32x2_t, u64>(vmovn_u64(transmute::<F64X2, uint64x2_t>(x))) };
    // The cast to `u64` reads the lanes in their order in memory, lane 0 first, so on the
    // big-endian targets (aarch64_be, tier 3, which no CI job builds) it gives
    // x0[31:0] << 32 | x1[31:0], and the halves are swapped back.
    let n = if cfg!(target_endian = "big") {
        n.rotate_left(32)
    } else {
        n
    };
    (n >> 31) as u32 & 0x3
}

pub(crate) fn ceil(x: F64X2) -> F64X2 {
    unsafe { vrndpq_f64(x) }
}

pub(crate) fn constant(x: f64, y: f64) -> F64X2 {
    unsafe { transmute([x, y]) }
}

// Inlined, as `add_rn` is.
#[inline(always)]
pub(crate) fn eq(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { transmute(vceqq_f64(x, y)) }
}

pub(crate) fn extract(x: F64X2) -> [f64; 2] {
    unsafe { transmute::<F64X2, [f64; 2]>(x) }
}

pub(crate) fn extract0(x: F64X2) -> f64 {
    unsafe { transmute::<F64X2, [f64; 2]>(x)[0] }
}

pub(crate) fn extract1(x: F64X2) -> f64 {
    unsafe { transmute::<F64X2, [f64; 2]>(x)[1] }
}

pub(crate) fn floor(x: F64X2) -> F64X2 {
    unsafe { vrndmq_f64(x) }
}

// Inlined, as the crate's operations inline it, where `Interval::classify` calls it. That
// function is `#[inline]`, so the call makes the crate export this one, and without this, a
// `*_with` method instantiated in another crate (see `src/simd/token.rs`) calls it out of line.
#[inline(always)]
pub(crate) fn ge(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { transmute(vcgeq_f64(x, y)) }
}

// Inlined, as `add_rn` is.
#[inline(always)]
pub(crate) fn gt(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { transmute(vcgtq_f64(x, y)) }
}

pub(crate) fn hadd_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { constant(vaddvq_f64(x), vaddvq_f64(y)) }
}

// Inlined, as `ge` is.
#[inline(always)]
pub(crate) fn le(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { transmute(vcleq_f64(x, y)) }
}

// Inlined, as `add_rn` is.
#[inline(always)]
pub(crate) fn lt(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { transmute(vcltq_f64(x, y)) }
}

// Inlined, as the crate's operations inline it, where a token's operation calls it (see
// `Baseline` in `src/simd/token.rs`). Without this, the call there makes the crate export it, and
// an operation instantiated in another crate calls it out of line.
#[inline(always)]
pub(crate) fn max(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vmaxnmq_f64(x, y) }
}

pub(crate) fn maximum(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vmaxq_f64(x, y) }
}

pub(crate) fn min(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vminnmq_f64(x, y) }
}

pub(crate) fn minimum(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vminq_f64(x, y) }
}

pub(crate) fn neg(x: F64X2) -> F64X2 {
    unsafe { vnegq_f64(x) }
}

pub(crate) fn neg0(x: F64X2) -> F64X2 {
    constant(-extract0(x), extract1(x))
}

// Inlined, as `add_rn` is.
#[inline(always)]
pub(crate) fn or(x: F64X2, y: F64X2) -> F64X2 {
    unsafe {
        transmute(vorrq_u64(
            transmute::<F64X2, uint64x2_t>(x),
            transmute::<F64X2, uint64x2_t>(y),
        ))
    }
}

pub(crate) fn round(x: F64X2) -> F64X2 {
    unsafe { vrndaq_f64(x) }
}

pub(crate) fn round_ties_even(x: F64X2) -> F64X2 {
    unsafe { vrndnq_f64(x) }
}

pub(crate) fn shuffle02(x: F64X2, y: F64X2) -> F64X2 {
    constant(extract0(x), extract0(y))
}

pub(crate) fn shuffle03(x: F64X2, y: F64X2) -> F64X2 {
    constant(extract0(x), extract1(y))
}

pub(crate) fn shuffle13(x: F64X2, y: F64X2) -> F64X2 {
    constant(extract1(x), extract1(y))
}

pub(crate) fn splat(x: f64) -> F64X2 {
    unsafe { transmute([x, x]) }
}

// Inlined, as `add_rn` is.
#[inline(always)]
pub(crate) fn sub_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vsubq_f64(x, y) }
}

pub(crate) fn swap(x: F64X2) -> F64X2 {
    shuffle12(x, x)
}

pub(crate) fn trunc(x: F64X2) -> F64X2 {
    unsafe { vrndq_f64(x) }
}

fn shuffle12(x: F64X2, y: F64X2) -> F64X2 {
    constant(extract1(x), extract0(y))
}

// The operations that round toward +∞ (and `sqrt_rd_ru` toward -∞ as well)
// compute the rounding explicitly, as `fma` on x86-64 does: see `aarch64/fma.rs`.
// The rounding mode in FPCR is never switched, except by the references of the
// differential tests (`impl_op_round!` in `aarch64/lanewise.rs`).
mod fma;
mod lanewise;
pub(crate) use fma::*;

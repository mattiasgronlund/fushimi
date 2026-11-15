use std::{
    arch::{aarch64::*, asm},
    mem::transmute,
};

pub(crate) const HAS_MAXIMUM: bool = true;

pub(crate) type F64X2 = float64x2_t;

pub(crate) fn abs(x: F64X2) -> F64X2 {
    unsafe { vabsq_f64(x) }
}

pub(crate) fn add_rn(x: F64X2, y: F64X2) -> F64X2 {
    unsafe { vaddq_f64(x, y) }
}

pub(crate) fn all(x: F64X2) -> bool {
    unsafe { transmute::<uint32x2_t, u64>(vmovn_u64(transmute::<F64X2, uint64x2_t>(x))) == !0u64 }
}

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

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞.
pub(crate) fn sqrt_rd_ru(x: F64X2) -> F64X2 {
    constant(sqrt1_rd(extract0(x)), sqrt1_ru(extract1(x)))
}

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

macro_rules! impl_op_round {
    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, rd) => {
        impl_op_round!($t, $f ($x $(,$y)*), $inst, 0x800000);
    };

    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, ru) => {
        impl_op_round!($t, $f ($x $(,$y)*), $inst, 0x400000);
    };

    ($t:ty, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, $fpcr:literal) => {
        pub(crate) fn $f(mut $x: $t, $($y: $t,)*) -> $t {
            unsafe {
                asm!(
                    "mrs {fpcr_bak}, fpcr",
                    "msr fpcr, {fpcr:x}",
                    $inst,
                    "msr fpcr, {fpcr_bak}",
                    $x = inout(vreg) $x,
                    $($y = in(vreg) $y,)*
                    fpcr = in(reg) $fpcr,
                    fpcr_bak = out(reg) _,
                    options(pure, nomem, nostack, preserves_flags)
                );
            }
            $x
        }
    };
}

impl_op_round!(f64, sqrt1_rd(x), "fsqrt {x:d}, {x:d}", rd);
impl_op_round!(f64, sqrt1_ru(x), "fsqrt {x:d}, {x:d}", ru);
impl_op_round!(f64, sub1_ru(x, y), "fsub {x:d}, {x:d}, {y:d}", ru);
impl_op_round!(F64X2, add_ru(x, y), "fadd.2d {x:v}, {x:v}, {y:v}", ru);
impl_op_round!(F64X2, sub_ru(x, y), "fsub.2d {x:v}, {x:v}, {y:v}", ru);
impl_op_round!(F64X2, mul_ru(x, y), "fmul.2d {x:v}, {x:v}, {y:v}", ru);
impl_op_round!(F64X2, div_ru(x, y), "fdiv.2d {x:v}, {x:v}, {y:v}", ru);

pub(crate) fn mul_add_ru(x: F64X2, y: F64X2, mut z: F64X2) -> F64X2 {
    unsafe {
        asm!(
            "mrs {fpcr_bak}, fpcr",
            "msr fpcr, {fpcr:x}",
            "fmla.2d {z:v}, {x:v}, {y:v}",
            "msr fpcr, {fpcr_bak}",
            x = in(vreg) x,
            y = in(vreg) y,
            z = inout(vreg) z,
            fpcr = in(reg) 0x400000,
            fpcr_bak = out(reg) _,
            options(pure, nomem, nostack, preserves_flags)
        );
    }
    z
}

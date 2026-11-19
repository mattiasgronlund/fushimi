use std::arch::asm;

macro_rules! impl_op_round {
    (
        @op $t:ty, $reg:ident, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, $er:literal
        $(, $d:ident in $dreg:tt)?
    ) => {
        // In a build without `avx512f`, this is the backend of the token `V4`
        // (`src/simd/token.rs`), whose copies inline it. rustc accepts a `zmm_reg` operand
        // only in a function that has `avx512f` itself, so this function cannot take the
        // target features of its caller as the `#[inline(always)]` ones of `fma` and `sse42`
        // do.
        #[cfg_attr(not(target_feature = "avx512f"), target_feature(enable = "avx512f"), inline)]
        pub(crate) fn $f(mut $x: $t, $($y: $t,)*) -> $t {
            unsafe {
                $(let $d: std::arch::x86_64::__m512d;)?
                asm!(
                    concat!($inst, ", ", $er),
                    $x = inout($reg) $x,
                    $($y = in($reg) $y,)*
                    $(out($dreg) $d,)?
                    options(pure, nomem, nostack, preserves_flags)
                );
                $x
            }
        }
    };

    // An operation on `zmm` registers. In a build without `avx512f`, `_dirty`, an output in
    // `zmm15` that is never read, shows LLVM that the instruction writes a `zmm` register: an
    // operand of type `__m128d` in `zmm_reg` is an `xmm` register to LLVM. LLVM puts a
    // `vzeroupper` before a call or return that follows a write of a `ymm` or `zmm` register
    // that it sees, unless the call or return itself passes one of these registers, as Intel's
    // optimization manual asks before code that may run SSE instructions. Without `_dirty`, the
    // regions of `V4` in a build for `x86-64` returned to its SSE code with no `vzeroupper`
    // (objdump, row 138). In a build with `avx512f`, the operations are left as they were:
    // LLVM compiles that build's code with VEX and EVEX encodings only, so only code from
    // outside it, such as the precompiled standard library or a C library, or an `asm!` block,
    // can run SSE instructions after them.
    ($t:ty, zmm_reg, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, ru) => {
        #[cfg(target_feature = "avx512f")]
        impl_op_round!(@op $t, zmm_reg, $f ($x $(,$y)*), $inst, "{{ru-sae}}");
        #[cfg(not(target_feature = "avx512f"))]
        impl_op_round!(@op $t, zmm_reg, $f ($x $(,$y)*), $inst, "{{ru-sae}}", _dirty in "zmm15");
    };

    ($t:ty, $reg:ident, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, rd) => {
        impl_op_round!(@op $t, $reg, $f ($x $(,$y)*), $inst, "{{rd-sae}}");
    };

    ($t:ty, $reg:ident, $f:ident ($x:ident $(,$y:ident)*), $inst:literal, ru) => {
        impl_op_round!(@op $t, $reg, $f ($x $(,$y)*), $inst, "{{ru-sae}}");
    };
}

impl_op_round!(f64, xmm_reg, sqrt1_rd(x), "vsqrtsd {x}, {x}, {x}", rd);
impl_op_round!(f64, xmm_reg, sqrt1_ru(x), "vsqrtsd {x}, {x}, {x}", ru);
impl_op_round!(f64, xmm_reg, sub1_ru(x, y), "vsubsd {x}, {x}, {y}", ru);

/// `sqrt_rd_ru([x0, x1]) = [√x0, √x1]`, the first rounded toward -∞ and the
/// second toward +∞. Embedded rounding applies to a whole instruction, so the
/// two lanes are done separately.
#[cfg_attr(
    not(target_feature = "avx512f"),
    target_feature(enable = "avx512f"),
    inline
)]
pub(crate) fn sqrt_rd_ru(x: super::F64X2) -> super::F64X2 {
    super::constant(sqrt1_rd(super::extract0(x)), sqrt1_ru(super::extract1(x)))
}
impl_op_round!(
    super::F64X2,
    zmm_reg,
    add_ru(x, y),
    "vaddpd {x:z}, {x:z}, {y:z}",
    ru
);
impl_op_round!(
    super::F64X2,
    zmm_reg,
    sub_ru(x, y),
    "vsubpd {x:z}, {x:z}, {y:z}",
    ru
);
impl_op_round!(
    super::F64X2,
    zmm_reg,
    mul_ru(x, y),
    "vmulpd {x:z}, {x:z}, {y:z}",
    ru
);
impl_op_round!(
    super::F64X2,
    zmm_reg,
    div_ru(x, y),
    "vdivpd {x:z}, {x:z}, {y:z}",
    ru
);
impl_op_round!(
    super::F64X2,
    zmm_reg,
    mul_add_ru(x, y, z),
    "vfmadd213pd {x:z}, {y:z}, {z:z}",
    ru
);

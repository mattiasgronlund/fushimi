// Tests of the accurate phase of x^y, `src/dyadic/pow/acc.rs`, and of its tables,
// `src/dyadic/pow/tables.rs`, against MPFR: the tables and the constants are what their
// comments say, the bounds of `acc_pow` hold x^y, and `acc_pow_dir` and `acc_pow_near` give
// MPFR's roundings wherever they return one, on arguments next to the exact cases, at the
// exact cases and at midpoints, and on random ones. `print_acc_tables` prints the
// tables for `tables.rs` and writes them to `rocq/theories/ModelPowTable.v`, and
// `acc_table_in_rocq` checks that file against `tables.rs`.

#![cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]

use super::super::acc::{acc_pow, acc_pow_dir, acc_pow_near, INV_LN2, LN2};
use super::super::tables::{ACC_G, ACC_LN, ACC_R, EXP_HI, EXP_LO};
use super::Rng;
use crate::mpfr_calls::mpfr::{pow_rd, pow_rn, pow_ru};
use rug::{float::Round, ops::Pow as _, Float, Integer};

// The precision of the values that the tables and the bounds are checked against, far above
// the 128 bits of the bounds.
const PREC: u32 = 1024;

fn floor(v: &Float) -> Integer {
    v.to_integer_round(Round::Down).unwrap().0
}

// The tables as their comments define them, from MPFR's values: ACC_R[i] = round(2^20 /
// (725 + 2 i)), the inverse of the middle of [(362 + i) / 512, (363 + i) / 512) rounded to an
// integer at 2^-10, but 1024 at i = 149 and 150; ACC_LN[i] = floor(-ln r 2^(127 + g)) for
// r = ACC_R[i] 2^-10 and the g = ACC_G[i] with 2^126 <= |ACC_LN[i]| <= 2^127, and 0 and g = 0
// where r = 1; EXP_HI[j] = floor(2^(j/64) 2^127) and EXP_LO[j] = floor(2^(j/4096) 2^127).
#[allow(clippy::type_complexity)] // The five tables, in the order of `tables.rs`.
fn acc_tables() -> (Vec<u16>, Vec<u8>, Vec<i128>, Vec<u128>, Vec<u128>) {
    let (mut r, mut g, mut t) = (vec![], vec![], vec![]);
    for i in 0..362u32 {
        let d = 725 + 2 * i;
        let ri = if i == 149 || i == 150 {
            1024
        } else {
            // round(2^20 / d) = floor((2^21 + d) / (2 d)), with no tie at an odd d.
            ((1 << 21) + d) / (2 * d)
        };
        r.push(u16::try_from(ri).unwrap());
        let mut v: Float = Float::with_val(PREC, ri) / 1024;
        v.ln_mut();
        v = -v;
        if v.is_zero() {
            g.push(0);
            t.push(0);
        } else {
            // |v| in [2^(x - 1), 2^x) for x = `get_exp`, so g = -x puts |v| 2^(127 + g) in
            // [2^126, 2^127).
            let gi = -v.get_exp().unwrap();
            g.push(u8::try_from(gi).unwrap());
            t.push(floor(&(v << (127 + gi))).to_i128().unwrap());
        }
    }
    let powers = |q: u32| -> Vec<u128> {
        (0..64)
            .map(|j| {
                let v = Float::with_val(PREC, 2).pow(Float::with_val(PREC, j) / q);
                floor(&(v << 127)).to_u128().unwrap()
            })
            .collect()
    };
    (r, g, t, powers(64), powers(4096))
}

// The tables of `tables.rs` and the constants of `acc.rs` are those of `acc_tables`, with
// |r m - 1| <= 2^-9 at both ends of each interval of m, and so on all of it, and |T| from
// 2^126 to 2^127 but where r = 1.
#[test]
fn acc_tables_and_constants() {
    let (r, g, t, hi, lo) = acc_tables();
    assert_eq!(ACC_R.to_vec(), r, "ACC_R");
    assert_eq!(ACC_G.to_vec(), g, "ACC_G");
    assert_eq!(ACC_LN.to_vec(), t, "ACC_LN");
    assert_eq!(EXP_HI.to_vec(), hi, "EXP_HI");
    assert_eq!(EXP_LO.to_vec(), lo, "EXP_LO");
    for (i, (&ri, &ti)) in ACC_R.iter().zip(&ACC_LN).enumerate() {
        let i = i64::try_from(i).unwrap();
        for end in [362 + i, 363 + i] {
            // r end / 512 - 1 = (R end - 2^19) 2^-19.
            let z = i64::from(ri) * end - (1 << 19);
            assert!(z.abs() <= 1 << 10, "ACC_R[{i}]: |r {end}/512 - 1| > 2^-9");
        }
        assert!(
            (ti == 0) == (ri == 1024) && (ti == 0 || (1 << 126) <= ti.unsigned_abs()),
            "ACC_LN[{i}]"
        );
    }
    let ln2 = Float::with_val(PREC, rug::float::Constant::Log2);
    assert_eq!(Some(LN2), floor(&(ln2.clone() << 128)).to_u128(), "LN2");
    let inv: Float = (Float::with_val(PREC, 1) / ln2) << 62;
    let inv = inv.to_integer_round(Round::Nearest).unwrap().0;
    assert_eq!(Some(INV_LN2), inv.to_i64(), "INV_LN2");
}

// The five tables as the strings of their entries, in the order of `tables.rs`: decimal for
// `ACC_R` and `ACC_G`, and hexadecimal, with a sign where negative, for the others.
fn table_strings(
    r: &[u16],
    g: &[u8],
    t: &[i128],
    hi: &[u128],
    lo: &[u128],
) -> [(&'static str, &'static str, Vec<String>); 5] {
    let hex = |v: i128| {
        if v < 0 {
            format!("-{:#034x}", v.unsigned_abs())
        } else {
            format!("{v:#034x}")
        }
    };
    let ux = |v: &[u128]| v.iter().map(|&v| format!("{v:#034x}")).collect();
    [
        ("ACC_R", "u16", r.iter().map(u16::to_string).collect()),
        ("ACC_G", "u8", g.iter().map(u8::to_string).collect()),
        ("ACC_LN", "i128", t.iter().map(|&v| hex(v)).collect()),
        ("EXP_HI", "u128", ux(hi)),
        ("EXP_LO", "u128", ux(lo)),
    ]
}

// `rocq/theories/ModelPowTable.v` for the given tables: each a `list Z`, four entries to a
// line, with a space after the sign of a negative entry.
fn model_pow_table_v(r: &[u16], g: &[u8], t: &[i128], hi: &[u128], lo: &[u128]) -> String {
    let mut s = String::from(
        "(** Generated by the test [print_acc_tables] of\n    \
         [src/dyadic/pow/tests/acc.rs], which prints [src/dyadic/pow/tables.rs]\n    \
         too: change that test, not this file. The test [acc_table_in_rocq]\n    \
         checks that this file transcribes the tables [ACC_R], [ACC_G],\n    \
         [ACC_LN], [EXP_HI] and [EXP_LO] of [tables.rs], whose comment says\n    \
         what they hold. [Model.v] reads them as [DyadicPow.ACC_R] and so on. *)\n\n\
         From Stdlib Require Import ZArith List.\n\
         Import ListNotations.\n\
         Open Scope Z_scope.\n",
    );
    for (name, _, items) in table_strings(r, g, t, hi, lo) {
        let items: Vec<String> = items.into_iter().map(|v| v.replace('-', "- ")).collect();
        let lines: Vec<String> = items
            .chunks(4)
            .map(|c| format!("  {}", c.join("; ")))
            .collect();
        s += &format!(
            "\nDefinition {name} : list Z := [\n{}\n].\n",
            lines.join(";\n")
        );
    }
    s
}

// `rocq/theories/ModelPowTable.v`, which the proofs read the tables from, is what
// `model_pow_table_v` makes of the tables of `tables.rs`. `rocq/` is not in the package that
// `cargo package` makes, so where the file is missing there is nothing to check.
#[test]
fn acc_table_in_rocq() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/rocq/theories/ModelPowTable.v");
    let Ok(file) = std::fs::read_to_string(path) else {
        return;
    };
    assert!(
        file == model_pow_table_v(&ACC_R, &ACC_G, &ACC_LN, &EXP_HI, &EXP_LO),
        "rocq/theories/ModelPowTable.v does not transcribe the tables of `tables.rs`: run the \
         test `print_acc_tables`"
    );
}

// Prints the tables of `acc_tables` for `tables.rs`, and writes them to
// `rocq/theories/ModelPowTable.v`. Run by hand, with `--ignored --nocapture`.
#[test]
#[ignore]
fn print_acc_tables() {
    let (r, g, t, hi, lo) = acc_tables();
    for (name, ty, items) in table_strings(&r, &g, &t, &hi, &lo) {
        println!("pub(super) const {name}: [{ty}; {}] = [", items.len());
        for v in items {
            println!("    {v},");
        }
        println!("];");
    }
    let root = env!("CARGO_MANIFEST_DIR");
    std::fs::write(
        format!("{root}/rocq/theories/ModelPowTable.v"),
        model_pow_table_v(&r, &g, &t, &hi, &lo),
    )
    .unwrap();
}

// x^y rounded down and up at `PREC` bits by MPFR.
fn mpfr_pow(x: f64, y: f64) -> (Float, Float) {
    let (x, y) = (Float::with_val(PREC, x), Float::with_val(PREC, y));
    let at = |r| Float::with_val_round(PREC, (&x).pow(&y), r).0;
    (at(Round::Down), at(Round::Up))
}

// Checks `acc_pow` and the two roundings at (x, y), and returns log2 of the relative width of
// the bounds, or `None` where the phase declined.
fn check(x: f64, y: f64) -> Option<f64> {
    let what = format!("acc_pow({x:e}, {y:e})");
    let dir = [acc_pow_dir(x, y, false), acc_pow_dir(x, y, true)];
    let near = acc_pow_near(x, y);
    let Some((lo, hi, e)) = acc_pow(x, y) else {
        assert!(dir == [None, None] && near.is_none(), "{what}: declined");
        return None;
    };
    assert!(1 << 126 <= lo && lo <= hi, "{what}: ({lo:#x}, {hi:#x})");
    let e = i32::try_from(e).unwrap();
    let (vl, vh) = mpfr_pow(x, y);
    let (fl, fh) = (
        Float::with_val(PREC, lo) << e,
        Float::with_val(PREC, hi) << e,
    );
    assert!(
        fl <= vl && vh <= fh,
        "{what}: ({lo:#x}, {hi:#x}) 2^{e} does not hold x^y"
    );
    for (v, want) in dir.iter().zip([pow_rd(x, y), pow_ru(x, y)]) {
        assert!(
            v.is_none_or(|v| v.to_bits() == want.to_bits()),
            "{what}: {v:?} != MPFR's {want:e}"
        );
    }
    let want = pow_rn(x, y);
    assert!(
        near.is_none_or(|v| v.to_bits() == want.to_bits()),
        "{what}: {near:?} to nearest != MPFR's {want:e}"
    );
    let w = Float::with_val(PREC, hi - lo) / lo;
    Some(w.to_f64().log2())
}

// Checks each of `args` and prints how often the phase declined, how often each rounding
// passed, and the widest bounds.
fn check_all(name: &str, args: impl Iterator<Item = (f64, f64)>) {
    let (mut n, mut declined, mut passed, mut widest) = (0, 0, [0; 3], f64::NEG_INFINITY);
    for (x, y) in args {
        n += 1;
        match check(x, y) {
            None => declined += 1,
            Some(w) => widest = widest.max(w),
        }
        for (p, v) in passed.iter_mut().zip([
            acc_pow_dir(x, y, false),
            acc_pow_dir(x, y, true),
            acc_pow_near(x, y),
        ]) {
            *p += usize::from(v.is_some());
        }
    }
    println!(
        "{name}: {n} arguments, {declined} declined, passed rd/ru/rn {passed:?}, widest 2^{widest:.2}"
    );
}

// Arguments near the exact cases: x = q^2 with y = ±1/2 and ±3/2 and x = q^4, rounded to an
// `f64`, with y = ±1/4 and 3/4, for odd q below 2^20, x = 2^k with y = 1/2, and x = 1 with
// y = 2^k + 1/2 for k up to 39, each x moved by -3 to 3 ulps. Some of these x^y are within
// 2^-67 of x^y of an `f64`, where the directed tests of the fast path can fail, or of a
// midpoint, where its test to nearest can: those that are `f64`s, and x^y at x = 2^k for an
// even k and at x next to 1 for k up to 17.
#[test]
fn acc_pow_near_exact() {
    let mut rng = Rng(0x5eed_acc0);
    let args = (0..20_000).map(|_| {
        let q = (rng.below(1 << 20) | 1) as f64;
        let d = rng.below(7) as i64 - 3;
        let (x, y) = match rng.below(4) {
            0 => (q * q, [0.5, -0.5, 1.5, -1.5][rng.below(4) as usize]),
            1 => (q * q * q * q, [0.25, -0.25, 0.75][rng.below(3) as usize]),
            2 => (2f64.powi(rng.below(200) as i32 - 100), 0.5),
            _ => (1.0, (1u64 << rng.below(40)) as f64 + 0.5),
        };
        (f64::from_bits(x.to_bits().wrapping_add_signed(d)), y)
    });
    check_all("near exact", args.filter(|&(x, _)| x > 0.0 && x != 1.0));
}

// The phase declines where its rounding test must fail. At the exact cases, where y is not an
// integer and x^y is an `f64`: x = q^2 with y = 1/2 for odd q below 2^26, x = q^4 with y = 1/4
// and 3/4 for odd q below 2^13, and x = 4^k with y = 1/2. Where neither bound is x^y itself,
// lo < x^y < hi, so that lo and hi round to two different `f64`s in either direction, and
// both directed roundings decline; to nearest both may round to x^y. At the midpoints: x = t^2
// for odd t from 208065 to 262143 and y = 3/2, where x^y = t^3 is odd and from 2^53 to 2^54
// (208063^3 < 2^53 < 208065^3), and so 54 bits long. There lo and hi round to nearest to the
// two `f64`s next to x^y, and `acc_pow_near` declines; the directed roundings may pass. A
// bound that is x^y itself could let a rounding pass, correctly, which the theorems allow; on
// these arguments none does.
#[test]
fn acc_pow_declines() {
    let mut rng = Rng(0xacc0_dec1);
    let mut odd = |below: u64| loop {
        let q = rng.below(below) | 1;
        if q >= 3 {
            break q as f64;
        }
    };
    let squares: Vec<_> = (0..1000)
        .map(|_| {
            let q = odd(1 << 26);
            (q * q, 0.5, q)
        })
        .collect();
    let fourths: Vec<_> = (0..500)
        .flat_map(|_| {
            let q = odd(1 << 13);
            let x = q * q * q * q;
            [(x, 0.25, q), (x, 0.75, q * q * q)]
        })
        .collect();
    let twos: Vec<_> = (-500..=500)
        .filter(|&k| k != 0)
        .map(|k| (2f64.powi(2 * k), 0.5, 2f64.powi(k)))
        .collect();
    for (name, args) in [
        ("exact q^2", squares),
        ("exact q^4", fourths),
        ("exact 4^k", twos),
    ] {
        for &(x, y, v) in &args {
            let what = format!("acc_pow({x:e}, {y:e})");
            // MPFR's roundings agree only where x^y is an `f64`.
            assert!(
                pow_rd(x, y) == v && pow_ru(x, y) == v,
                "{what}: x^y != {v:e}"
            );
            let dir = [acc_pow_dir(x, y, false), acc_pow_dir(x, y, true)];
            assert!(dir == [None, None], "{what}: {dir:?} at the exact x^y");
            let near = acc_pow_near(x, y);
            assert!(near.is_none_or(|w| w == v), "{what}: {near:?} != {v:e}");
        }
        check_all(name, args.into_iter().map(|(x, y, _)| (x, y)));
    }
    let midpoints: Vec<_> = (208_065..=262_143u64)
        .step_by(16)
        .map(|t| {
            let c = t * t * t;
            assert!(c % 2 == 1 && (1 << 53..1 << 54).contains(&c), "{t}^3");
            let x = (t * t) as f64;
            // The two `f64`s next to x^y, exact as they are even and below 2^54.
            let (dn, up) = ((c - 1) as f64, (c + 1) as f64);
            let what = format!("acc_pow({x:e}, 1.5)");
            assert!(
                pow_rd(x, 1.5) == dn && pow_ru(x, 1.5) == up,
                "{what}: x^y != {c}"
            );
            let near = acc_pow_near(x, 1.5);
            assert!(near.is_none(), "{what}: {near:?} at the midpoint x^y");
            (x, 1.5)
        })
        .collect();
    check_all("midpoints", midpoints.into_iter());
}

// Random arguments: x of random bits over the positive finite `f64`s and y = ±u 2^k for u in
// [1, 2) and k from -60 to 10, kept where |y ln x| <= 800, and x in [1/2, 2) with k up to 40,
// each but at the integers of `i32`, which `pow` passes to x^n.
#[test]
fn acc_pow_random() {
    let mut rng = Rng(0xacc0_5eed);
    let args: Vec<(f64, f64)> = (0..20_000)
        .map(|_| {
            let unit = |r: &mut Rng| f64::from_bits(r.next() >> 12 | 0x3ff0_0000_0000_0000);
            let (x, k) = if rng.below(2) == 0 {
                let x = f64::from_bits(rng.below(0x7ff0_0000_0000_0000 - 1) + 1);
                (x, rng.below(71) as i32 - 60)
            } else {
                (
                    unit(&mut rng) * [0.5, 1.0][rng.below(2) as usize],
                    rng.below(41) as i32,
                )
            };
            let y = unit(&mut rng) * 2f64.powi(k);
            (x, if rng.below(2) == 0 { y } else { -y })
        })
        .filter(|&(x, y)| (y * x.ln()).abs() <= 800.0 && f64::from(y as i32) != y)
        .collect();
    check_all("random", args.into_iter());
}

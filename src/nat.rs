// A natural number of any size, for the bounds of interval literals in `src/parse.rs` and the
// digits of the bounds that `src/format.rs` prints.
//
// A `Nat` is its 64-bit limbs, the least significant first, with no zero limb at the top, so
// that 0 has no limbs and each number has exactly one representation. Products of limbs, with
// their carries, are computed in `u128`, by the loops of `src/limbs.rs` and, for `from_dec`, by
// `mul_add_u128` below. `rocq/theories/Model.v` transcribes the operations below that `scale`
// in `src/parse.rs` and the functions of `src/format/digits.rs` call, `from_limbs`, `from_u64`,
// `is_zero`, `bits`, `low_u128`, `pow5` with `mul_add_u64`, `div_rem`, `cmp`, `+`, `*`, `<<`
// and `>>`, so it has to be updated along with them. `rocq/theories/NatOps.v` proves, with the
// theorems about the loops in `rocq/theories/Limbs.v` and `rocq/theories/Knuth.v`, that each
// computes its operation on integers and returns limbs with no zero limb at the top.
// `from_dec`, with `dec_chunks`, `dec_u128`, `mul_add_u128`, `push_u128` and `dec_limbs`, which
// only `from_dec` uses, `from_hex` and `-`, with which the grammar of `src/parse.rs` and
// `src/parse/rat.rs` compute the bounds of a literal, and `to_dec`, with `div_rem_ten19`,
// `div_ten19`, `top_digits` and `write_digits`, which only the layout of the printed text uses,
// are not modelled; that `from_dec`, `from_hex` and `-` return no zero limb at the top, and that
// `div_rem_ten19` leaves none, is checked by reading. The tests at the end compare them all with
// `rug::Integer`, and the steps of `to_dec` also with the arithmetic of `u128` and the `Display`
// of `u64`.

use crate::limbs;
use std::{
    cmp::Ordering,
    ops::{Add, Mul, Shl, Shr, Sub},
};

// With no zero limb at the top, the derived `PartialEq` compares values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Nat(Vec<u64>);

impl Nat {
    // The `Nat` of the limbs `v`, without the zero limbs at the top.
    fn from_limbs(mut v: Vec<u64>) -> Self {
        while v.last() == Some(&0) {
            v.pop();
        }
        Self(v)
    }

    /// `x` as a `Nat`.
    pub(crate) fn from_u64(x: u64) -> Self {
        Self::from_limbs(vec![x])
    }

    /// The number that the decimal digits `s` spell, which the grammar makes nonempty.
    pub(crate) fn from_dec(s: &str) -> Self {
        let s = s.as_bytes();
        if s.len() <= 19 {
            // Below 10^19 < 2^64: one limb, or none for 0.
            let mut x = Vec::new();
            push_u128(&mut x, u128::from(digits(s, 10)));
            return Self(x);
        }
        // The first digits, at most `DEC_CUTOFF`, 38 at a time by `dec_chunks`, and the others
        // 19 at a time, n * 10^19 + the next 19, by `mul_add_u64`. Up to `DEC_CUTOFF` digits
        // there are no others; above it the others are a multiple of 19 that leaves
        // DEC_CUTOFF - 18 to DEC_CUTOFF first digits, so fewer than all. One pass of
        // `mul_add_u128` over the limbs of `n` for 38 digits, in place of two of `mul_add_u64`,
        // saves the cost of a pass, but each of its steps takes two products of limbs, and once
        // `n` is long, reading the digits 19 at a time took fewer instructions (see
        // `DEC_CUTOFF`).
        let rest = s.len().saturating_sub(DEC_CUTOFF).div_ceil(19) * 19;
        let (head, tail) = s.split_at(s.len() - rest);
        // Room for every limb, so that the loop below does not grow the `Vec` either.
        let mut n = Self(dec_chunks(head, dec_limbs(s.len())));
        // `mul_add_u64` keeps the top limb nonzero, and an `n` of 0, which has no limbs, gets
        // the chunk as its limb if the chunk is not 0.
        for c in tail.chunks_exact(19) {
            n.mul_add_u64(TEN19, digits(c, 10));
        }
        n
    }

    /// The number that the hexadecimal digits `s` spell, which the grammar makes nonempty.
    pub(crate) fn from_hex(s: &str) -> Self {
        // 16 digits make a limb, from the last digit up.
        Self::from_limbs(s.as_bytes().rchunks(16).map(|c| digits(c, 16)).collect())
    }

    /// `self == 0`.
    pub(crate) fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// The number of bits of `self`, which is 0 for 0: `2^(b - 1) <= self < 2^b` otherwise.
    pub(crate) fn bits(&self) -> u64 {
        limbs::bit_len(&self.0)
    }

    /// `self mod 2^128`.
    pub(crate) fn low_u128(&self) -> u128 {
        let limb = |i| u128::from(self.0.get(i).copied().unwrap_or(0));
        limb(0) | limb(1) << 64
    }

    /// `5^k`.
    pub(crate) fn pow5(k: u32) -> Self {
        // 5^k = 5^(k mod 27) * (5^27)^(k / 27), where 5^27 is the largest power of 5 below
        // 2^64: one multiplication by a limb at a time, in place, in a `Vec` that has room for
        // every limb of 5^k from the start. These are about k^2/1500 products of limbs, more
        // than the k^2/2300 of binary powering with schoolbook squares, but each costs less,
        // and no square needs a new `Vec`. On an x86-64 machine, this took less time for each
        // k from 27 to 10^6 that was timed: a sixth at k = 300 and 0.84 at k = 10^6. A
        // multiplication faster than schoolbook would change that for large k.
        const K: u32 = 27;
        let mut p = Self(Vec::with_capacity(pow5_limbs(k)));
        p.0.push(5u64.pow(k % K));
        for _ in 0..k / K {
            p.mul_add_u64(5u64.pow(K), 0);
        }
        p
    }

    /// `(self / d, self % d)`, the quotient rounded down. Panics if `d` is 0.
    pub(crate) fn div_rem(&self, d: &Nat) -> (Nat, Nat) {
        assert!(!d.is_zero(), "division by zero");
        let mut q = vec![0; self.0.len()];
        let mut r = vec![0; d.0.len()];
        let mut scratch = vec![0; self.0.len() + d.0.len() + 2];
        limbs::div_rem(&mut q, &mut r, &self.0, &d.0, &mut scratch);
        (Self::from_limbs(q), Self::from_limbs(r))
    }

    /// The decimal digits of `self`, with no zero in front, and `"0"` for 0.
    pub(crate) fn to_dec(&self) -> String {
        // The remainders of repeated divisions by 10^19 < 2^64 are the chunks of 19 digits,
        // from the last one up, until one limb, `top`, is left, which is printed without
        // zeros in front: up to 20 digits. A number of one limb is its `top`, so it takes no
        // division by 10^19, nor a copy of its limbs or a `Vec` of chunks.
        let (top, chunks) = match self.0[..] {
            [] => return String::from("0"),
            [l] => (l, Vec::new()),
            _ => {
                // 10^(19 c) <= self < 2^(64 n) for `c` chunks and `n` limbs, so
                // c < 64 n log10(2) / 19 < 1.014 n, which leaves room for the chunks of up to
                // 71 limbs, more than `src/format.rs` prints.
                let mut chunks = Vec::with_capacity(self.0.len() + 1);
                let mut x = self.0.clone();
                // A quotient of `x >= 2^64` is at least 2^64 / 10^19 > 1, so `x` keeps a limb.
                while x.len() > 1 {
                    chunks.push(div_rem_ten19(&mut x));
                }
                (x[0], chunks)
            }
        };
        // `top` and the chunks from the top one down, appended to a `Vec` made with room for
        // all of them, so that it is allocated once and not zeroed first.
        let (t, n) = top_digits(top);
        let mut s = Vec::with_capacity(n + 19 * chunks.len());
        s.extend_from_slice(&t[20 - n..]);
        for &c in chunks.iter().rev() {
            let mut d = [0; 19];
            write_digits(&mut d, c);
            s.extend_from_slice(&d);
        }
        // ASCII digits, which are UTF-8.
        String::from_utf8(s).unwrap()
    }

    // `self := self * m + a` for `m > 0`, which keeps the top limb nonzero.
    fn mul_add_u64(&mut self, m: u64, a: u64) {
        debug_assert!(m > 0);
        let carry = limbs::mul_add_limb(&mut self.0, m, a);
        if carry != 0 {
            self.0.push(carry);
        }
    }
}

// 10^19, the largest power of 10 below 2^64, which is at least 2^63.
const TEN19: u64 = 10u64.pow(19);

// `x := x / 10^19` and returns `x % 10^19`, for the limbs `x` of a `Nat`, which keep no zero
// limb at the top.
fn div_rem_ten19(x: &mut Vec<u64>) -> u64 {
    // From the top limb down: `r < 10^19`, so `(r * 2^64 + l) / 10^19 < 2^64`.
    let mut r = 0;
    for l in x.iter_mut().rev() {
        (*l, r) = div_ten19(r, *l);
    }
    // x / 10^19 >= x / 2^64, which has one limb less than `x`, so at most the top limb is 0.
    if x.last() == Some(&0) {
        x.pop();
    }
    r
}

// `(u / 10^19, u % 10^19)` for `u = u1 * 2^64 + u0` with `u1 < 10^19`, by the division of
// two limbs by one with a reciprocal, Algorithm 4 of Möller and Granlund, "Improved division
// by invariant integers", IEEE Transactions on Computers 60(2), 2011. 10^19 >= 2^63 is
// normalized, so no shift is needed.
fn div_ten19(u1: u64, u0: u64) -> (u64, u64) {
    // The reciprocal v = floor((2^128 - 1) / d) - 2^64, below 2^64 as d >= 2^63.
    const V: u64 = (u128::MAX / TEN19 as u128 - (1 << 64)) as u64;
    let d = TEN19;
    // (q1, q0) := v * u1 + u, which is below 2^128: it is u1 * floor((2^128 - 1) / d) + u0.
    let q = u128::from(V) * u128::from(u1) + (u128::from(u1) << 64 | u128::from(u0));
    // The candidate quotient q1 + 1 is at most one away from the quotient, and its remainder,
    // computed mod 2^64, tells which way: the paper shows that the two corrections below give
    // the quotient and the remainder.
    let mut q1 = ((q >> 64) as u64).wrapping_add(1);
    let mut r = u0.wrapping_sub(q1.wrapping_mul(d));
    if r > q as u64 {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if r >= d {
        q1 += 1;
        r -= d;
    }
    (q1, r)
}

// "00", "01", ..., "99" as ASCII: the two digits of each number below 100, which the
// `Display` of the integers in `core` reads from a table too, so that a division by 100 gives
// two digits.
const DEC_PAIRS: [[u8; 2]; 100] = {
    let mut t = [[0; 2]; 100];
    let mut i = 0;
    while i < 100 {
        t[i] = [b'0' + (i / 10) as u8, b'0' + (i % 10) as u8];
        i += 1;
    }
    t
};

// The decimal digits of `c < 10^out.len()` as ASCII, with zeros in front to fill `out`.
fn write_digits(out: &mut [u8], mut c: u64) {
    // Two digits at a time from the end, and the first one alone if `out.len()` is odd. Each
    // pass divides `c` by 100, so the one left for an odd `out.len()` is below 10.
    let mut pairs = out.rchunks_exact_mut(2);
    for o in &mut pairs {
        o.copy_from_slice(&DEC_PAIRS[(c % 100) as usize]);
        c /= 100;
    }
    if let [o] = pairs.into_remainder() {
        debug_assert!(c < 10);
        *o = b'0' + c as u8;
    }
}

// The decimal digits of `c`, with no zero in front, and "0" for 0: the last `n` bytes of the
// array, for the `n` that comes with it. A `u64` has at most 20 digits.
fn top_digits(c: u64) -> ([u8; 20], usize) {
    // `c > 0` has `ilog10(c) + 1` digits, so that `write_digits` writes them all, and no zero
    // in front. `c | 1` has as many: it is `c` for an odd `c`, and `c + 1` for an even one,
    // which is not 10^k - 1 (odd), so that `c + 1` is not 10^k. And `c | 1` is not 0, so
    // `ilog10` needs no test for 0, and 0 gets one digit.
    let n = (c | 1).ilog10() as usize + 1;
    let mut d = [0; 20];
    write_digits(&mut d[20 - n..], c);
    (d, n)
}

// At least the number of limbs of 5^k: log2(5) < 149/64, so 5^k has at most
// floor(149k/64) + 1 bits, and so at most floor(149k/4096) + 1 limbs.
fn pow5_limbs(k: u32) -> usize {
    // 149k < 2^40 fits a `u64`, and the bound, below 2^28, a `usize`.
    usize::try_from(u64::from(k) * 149 / 4096 + 1).unwrap()
}

// The value of the ASCII digits `s` in base `radix`, which has to fit a `u64`. Panics on a
// byte that is not a digit.
fn digits(s: &[u8], radix: u32) -> u64 {
    s.iter().fold(0, |n, &c| {
        n * u64::from(radix) + u64::from(char::from(c).to_digit(radix).unwrap())
    })
}

// 10^38, the largest power of 10 below 2^127.
const TEN38: u128 = 10u128.pow(38);

// The number of digits up to which `from_dec` reads them all 38 at a time. Of a longer number
// it reads the first `DEC_CUTOFF - 18` to `DEC_CUTOFF` digits 38 at a time, so that the
// others are a multiple of 19, and those 19 at a time. Of the cutoffs 1,000, 1,500, 2,000,
// 2,500 and 3,000, 1,000 took the fewest instructions to parse interval literals of 10^4 and
// 10^5 digits, as counted with cachegrind in a crate that links fushimi, built for Haswell
// and for x86-64: past the first 1,000 or so digits, reading them 19 at a time took fewer
// instructions than 38 at a time. Cutoffs below 1,000 were not counted.
const DEC_CUTOFF: usize = 1000;

// The limbs of the number that the ASCII decimal digits `s` spell, with no zero limb at the
// top, in a `Vec` made with room for `cap` limbs, so that `from_dec` can make room for the
// limbs that it adds after them too. Panics on a byte that is not a digit.
fn dec_chunks(s: &[u8], cap: usize) -> Vec<u64> {
    // 38 digits, below 10^38 < 2^127, at a time: x * 10^38 + the next 38. The first chunk
    // takes the digits left over, so that each of the others has 38, and is all of `s` for
    // fewer than 38 digits.
    let (head, tail) = s.split_at(s.len() % 38);
    let mut x = Vec::with_capacity(cap);
    push_u128(&mut x, dec_u128(head));
    // `x` holds the number that the digits so far spell, with no zero limb at the top. For a
    // nonzero `x` of `n` limbs, x * 10^38 >= 2^(64 (n - 1)) * 10^38 > 2^(64 n + 62), so the
    // carry is not 0, and its limbs pushed without a zero at the top keep the top limb
    // nonzero. For `x = 0` the carry is the chunk.
    for c in tail.chunks_exact(38) {
        let carry = mul_add_u128(&mut x, TEN38, dec_u128(c));
        push_u128(&mut x, carry);
    }
    x
}

// The number that the at most 38 ASCII decimal digits `s` spell, below 10^38: the digits in
// front of the last 19, of which there are at most 19, times 10^19, plus the last 19.
fn dec_u128(s: &[u8]) -> u128 {
    let (hi, lo) = s.split_at(s.len().saturating_sub(19));
    // (10^19 - 1) * 10^19 + 10^19 - 1 = 10^38 - 1 < 2^128.
    u128::from(digits(hi, 10)) * u128::from(TEN19) + u128::from(digits(lo, 10))
}

// `x := (x * m + c) mod 2^(64 x.len())` for `m < 2^127` and `c < 2^127`. Returns the limbs
// above the top one, `(x * m + c) >> (64 x.len())`, which is below 2^127.
fn mul_add_u128(x: &mut [u64], m: u128, mut c: u128) -> u128 {
    // m = m1 * 2^64 + m0 with m1 < 2^63.
    let m0 = u128::from(m as u64);
    let m1 = u128::from((m >> 64) as u64);
    // Limb by limb from the bottom: after `i` limbs, x[..i] + c * 2^(64 i) is the old x[..i]
    // times m plus the first c. For c = c1 * 2^64 + c0 and t = l * m0 + c0,
    // l * m + c = t + (l * m1 + c1) * 2^64, so the limb is t mod 2^64 and the next carry
    // l * m1 + c1 + t / 2^64.
    for l in x.iter_mut() {
        let l64 = u128::from(*l);
        // l * m0 + c0 <= (2^64 - 1)^2 + 2^64 - 1 < 2^128.
        let t = l64 * m0 + u128::from(c as u64);
        *l = t as u64;
        // l * m1 + c1 + t / 2^64 <= (2^64 - 1) (2^63 - 1) + 2^63 - 1 + 2^64 - 1 = 2^127 - 1,
        // as c1 < 2^63, so each sum stays below 2^128 and the carry below 2^127.
        c = l64 * m1 + (c >> 64) + (t >> 64);
    }
    c
}

// Pushes the limbs of `c` onto `x`, without a zero limb at the top: none for 0, one below
// 2^64 and two above.
fn push_u128(x: &mut Vec<u64>, c: u128) {
    if c != 0 {
        x.push(c as u64);
    }
    if c >> 64 != 0 {
        x.push((c >> 64) as u64);
    }
}

// At least the number of limbs of a number of `n` decimal digits: it is below 10^n, and
// log2(10) < 213/64, so it has at most floor(213n/64) + 1 bits, and so at most
// floor(213n/4096) + 1 limbs.
fn dec_limbs(n: usize) -> usize {
    // 213n fits a `u128`, and the bound, at most n for n > 0, a `usize`.
    (n as u128 * 213 / 4096) as usize + 1
}

impl Ord for Nat {
    fn cmp(&self, other: &Self) -> Ordering {
        // The derived `Ord` of `Vec` would compare the lowest limbs first.
        limbs::cmp(&self.0, &other.0)
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add<&Nat> for &Nat {
    type Output = Nat;

    fn add(self, rhs: &Nat) -> Nat {
        let (a, b) = if self.0.len() >= rhs.0.len() {
            (&self.0, &rhs.0)
        } else {
            (&rhs.0, &self.0)
        };
        // The limb more at the top takes the carry, so none leaves it.
        let mut out = Vec::with_capacity(a.len() + 1);
        out.extend_from_slice(a);
        out.push(0);
        limbs::add_assign(&mut out, b);
        Nat::from_limbs(out)
    }
}

/// `self - rhs`. Panics if `rhs > self`.
impl Sub<&Nat> for &Nat {
    type Output = Nat;

    fn sub(self, rhs: &Nat) -> Nat {
        assert!(self >= rhs, "subtraction below zero");
        // With no zero limb at the top, `rhs` has no more limbs than `self`.
        let mut out = self.0.clone();
        limbs::sub_assign(&mut out, &rhs.0, false);
        Nat::from_limbs(out)
    }
}

impl Mul<&Nat> for &Nat {
    type Output = Nat;

    // The `+` adds the numbers of limbs of the factors, which the product has room for.
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, rhs: &Nat) -> Nat {
        let mut out = vec![0; self.0.len() + rhs.0.len()];
        limbs::mul_into(&mut out, &self.0, &rhs.0);
        Nat::from_limbs(out)
    }
}

/// `self * 2^rhs`.
impl Shl<u64> for &Nat {
    type Output = Nat;

    fn shl(self, rhs: u64) -> Nat {
        if self.is_zero() {
            return Nat(Vec::new());
        }
        // `rhs / 64` zero limbs, then the limbs shifted by the remaining bits, with a limb more
        // for the bits that leave the top.
        let j = usize::try_from(rhs / 64).unwrap();
        let mut out = vec![0; j + self.0.len() + 1];
        limbs::shl_into(&mut out, &self.0, rhs);
        Nat::from_limbs(out)
    }
}

/// `self / 2^rhs`, rounded down.
impl Shr<u64> for &Nat {
    type Output = Nat;

    // The `/` counts the limbs that the shift drops.
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shr(self, rhs: u64) -> Nat {
        // The limbs from limb `rhs / 64` up, shifted by the remaining bits: the quotient is
        // below 2^(64 (n - rhs / 64)) for the `n` limbs of `self`.
        let j = usize::try_from(rhs / 64).unwrap_or(usize::MAX);
        let mut out = vec![0; self.0.len().saturating_sub(j)];
        limbs::shr_into(&mut out, &self.0, rhs);
        Nat::from_limbs(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn div_by_zero() {
        Nat::from_u64(1).div_rem(&Nat::from_u64(0));
    }

    #[test]
    #[should_panic]
    fn sub_below_zero() {
        let _ = &Nat::from_limbs(vec![0, 1]) - &Nat::from_limbs(vec![1, 1]);
    }

    #[test]
    fn ord_by_value() {
        // The derived `Ord` of the limbs would say `[1, 2] < [2, 1]`.
        let x = Nat::from_limbs(vec![1, 2]);
        let y = Nat::from_limbs(vec![2, 1]);
        assert!(x > y);
        assert!(Nat::from_limbs(vec![0, 1]) > Nat::from_u64(u64::MAX));
        assert_eq!(x.cmp(&x.clone()), Ordering::Equal);
    }

    #[test]
    fn low_u128() {
        for (v, x) in [
            (vec![], 0),
            (vec![7], 7),
            (vec![1, 2], 2 << 64 | 1),
            (vec![u64::MAX, u64::MAX, 3], u128::MAX),
        ] {
            assert_eq!(Nat::from_limbs(v).low_u128(), x);
        }
    }

    #[test]
    fn divisor_longer_than_dividend() {
        let x = Nat::from_limbs(vec![u64::MAX; 3]);
        let y = Nat::from_limbs(vec![0, 0, 0, 1]);
        let (q, r) = x.div_rem(&y);
        assert!(q.is_zero());
        assert_eq!(r, x);
    }
}

// The tests that compare with `rug`, a dev-dependency only on 64-bit Linux and macOS.
#[cfg(all(
    test,
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
mod rug_tests {
    use super::*;
    use rug::{integer::Order, Integer};

    struct Rng(u64);

    impl Rng {
        // SplitMix64.
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }

        // A limb that is often 0, 1, 2^63 or all ones, to make carries and borrows run
        // across limbs.
        fn limb(&mut self) -> u64 {
            match self.below(8) {
                0 => 0,
                1 => 1,
                2 => 1 << 63,
                3 | 4 => u64::MAX,
                _ => self.next(),
            }
        }

        // A `Nat` of up to `max` limbs, whose top limb is often 1.
        fn nat(&mut self, max: u64) -> Nat {
            let len = self.below(max + 1) as usize;
            let mut v: Vec<u64> = (0..len).map(|_| self.limb()).collect();
            if len > 0 && self.below(4) == 0 {
                v[len - 1] = 1;
            }
            Nat::from_limbs(v)
        }
    }

    // The number of random cases, which can be set with `FUSHIMI_PARSE_N`.
    fn n_cases() -> u64 {
        std::env::var("FUSHIMI_PARSE_N")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(if cfg!(debug_assertions) {
                1_000
            } else {
                10_000
            })
    }

    // The random numbers of the test numbered `test`, which the seed `FUSHIMI_PARSE_SEED`
    // changes. Without it, they are those of `Rng(test)`.
    fn rng(test: u64) -> Rng {
        let seed = std::env::var("FUSHIMI_PARSE_SEED")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        Rng(seed.wrapping_add(test))
    }

    fn int(x: &Nat) -> Integer {
        Integer::from_digits(&x.0, Order::Lsf)
    }

    fn nat(x: &Integer) -> Nat {
        assert!(*x >= 0);
        let mut v = vec![0; x.significant_digits::<u64>()];
        x.write_digits(&mut v, Order::Lsf);
        Nat::from_limbs(v)
    }

    // `x` has no zero limb at the top and is `y`.
    fn check(x: &Nat, y: &Integer) {
        assert_ne!(x.0.last(), Some(&0), "not normalized: {:?}", x);
        assert_eq!(int(x), *y);
    }

    // `to_dec` of `x` is the decimal digits that `rug` prints.
    fn check_dec(x: &Nat) {
        assert_eq!(x.to_dec(), int(x).to_string());
    }

    // 10^k = 5^k * 2^k.
    fn pow10(k: u32) -> Nat {
        &Nat::pow5(k) << u64::from(k)
    }

    // Each operation of `x` and `y`, and of `x` and the shifts in `shifts`, against `rug`.
    fn check_ops(x: &Nat, y: &Nat, shifts: &[u64]) {
        let (a, b) = (int(x), int(y));
        check(&(x + y), &Integer::from(&a + &b));
        check(&(x * y), &Integer::from(&a * &b));
        assert_eq!(x.cmp(y), a.cmp(&b), "{:?} {:?}", x, y);
        assert_eq!(x == y, a == b);
        if a >= b {
            check(&(x - y), &Integer::from(&a - &b));
        }
        if b != 0 {
            let (q, r) = x.div_rem(y);
            let (qq, rr) = a.clone().div_rem_floor(b.clone());
            check(&q, &qq);
            check(&r, &rr);
            // The quotient and the remainder of a product plus a remainder.
            let p = &(x * y) + &r;
            let (q, r2) = p.div_rem(y);
            check(&q, &a);
            check(&r2, &rr);
        }
        assert_eq!(x.bits(), u64::from(a.significant_bits()));
        assert_eq!(x.low_u128(), a.to_u128_wrapping());
        assert_eq!(x.is_zero(), a == 0);
        for &s in shifts {
            check(&(x << s), &Integer::from(&a << u32::try_from(s).unwrap()));
            check(&(x >> s), &Integer::from(&a >> u32::try_from(s).unwrap()));
        }
    }

    // Numbers whose limbs carry and borrow at every step, or have their top limb 1, and the
    // single limbs.
    fn patterns() -> Vec<Nat> {
        let m = u64::MAX;
        let h = 1 << 63;
        let mut v = vec![
            vec![],
            vec![1],
            vec![2],
            vec![h],
            vec![m],
            vec![m - 1],
            vec![0, 1],
            vec![1, 1],
            vec![m, 1],
            vec![0, h],
            vec![m, h],
            vec![1, 2],
            vec![2, 1],
            vec![0, 0, 1],
            vec![m, m, 1],
            vec![1, 0, 0, 1],
            vec![m, 0, m],
            vec![0, m, 0, h],
            vec![5, 0, 0, h],
            vec![m - 1, m, m, m],
        ];
        for k in 1..=6 {
            v.push(vec![m; k]);
            let mut w = vec![0; k];
            w.push(1);
            v.push(w);
        }
        v.into_iter().map(Nat::from_limbs).collect()
    }

    #[test]
    fn small() {
        check(&Nat::from_u64(0), &Integer::new());
        assert!(Nat::from_u64(0).is_zero());
        for x in [1, 2, 10, 1 << 63, u64::MAX] {
            check(&Nat::from_u64(x), &Integer::from(x));
        }
    }

    #[test]
    fn ops_on_patterns() {
        let shifts = [0, 1, 63, 64, 65, 127, 128, 129, 1000, 100_000];
        let p = patterns();
        for x in &p {
            for y in &p {
                check_ops(x, y, &shifts);
            }
        }
    }

    #[test]
    fn zero_operands() {
        let zero = Nat::from_u64(0);
        let x = Nat::from_limbs(vec![3, 0, 7]);
        check(&(&zero + &zero), &Integer::new());
        check(&(&zero - &zero), &Integer::new());
        check(&(&x - &zero), &int(&x));
        check(&(&x - &x), &Integer::new());
        check(&(&zero * &x), &Integer::new());
        check(&(&x * &zero), &Integer::new());
        let (q, r) = zero.div_rem(&x);
        check(&q, &Integer::new());
        check(&r, &Integer::new());
        // No limbs are made for 0, however far it is shifted.
        check(&(&zero << u64::MAX), &Integer::new());
        // Nor for a shift to the right past the top limb.
        check(&(&zero >> u64::MAX), &Integer::new());
        check(&(&x >> u64::MAX), &Integer::new());
        check(&(&x >> 192), &Integer::new());
        check(&(&x >> 191), &Integer::new());
        check(&(&x >> 130), &Integer::from(1));
        assert_eq!(zero.bits(), 0);
        assert_eq!(zero.low_u128(), 0);
    }

    #[test]
    fn bits_of_powers_of_two() {
        let one = Nat::from_u64(1);
        for k in 0..300 {
            let p = &one << k;
            assert_eq!(p.bits(), k + 1);
            assert_eq!((&p - &one).bits(), k);
            check(&p, &(Integer::from(1) << k as u32));
        }
    }

    #[test]
    fn pow5() {
        // Each `k` around a multiple of 27 up to 5400, where `pow5` takes one more factor
        // 5^27, and some above.
        let around_27 = (1..=200).flat_map(|m| [27 * m - 1, 27 * m, 27 * m + 1]);
        for k in (0..=300).chain(around_27).chain([12_345, 100_000]) {
            let p = Nat::pow5(k);
            check(&p, &Integer::from(Integer::u_pow_u(5, k)));
            // The `Vec` had room for every limb from the start.
            assert!(p.0.len() <= pow5_limbs(k), "{}", k);
        }
    }

    // The decimal and hexadecimal digits of `x`, after `zeros` zeros.
    fn digit_strings(x: &Integer, zeros: usize) -> [String; 2] {
        let z = "0".repeat(zeros);
        // The tests also take the hexadecimal digits in lower case, as the grammar takes both.
        [format!("{}{}", z, x), format!("{}{:X}", z, x)]
    }

    #[test]
    fn from_digits() {
        let ten = |k| Integer::from(Integer::u_pow_u(10, k));
        let mut cases = vec![
            Integer::new(),
            Integer::from(u64::MAX),
            Integer::from(u64::MAX) + 1,
            ten(19),
            ten(19) - 1,
            ten(38) - 1,
            ten(1000),
            Integer::from(Integer::u_pow_u(16, 64)) - 1,
        ];
        let mut rng = rng(1);
        for len in 1..200 {
            cases.push(int(&Nat::from_limbs(
                (0..len).map(|_| rng.limb()).collect(),
            )));
        }
        for x in &cases {
            for zeros in [0, 1, 18, 19, 20, 100] {
                let [dec, hex] = digit_strings(x, zeros);
                check(&Nat::from_dec(&dec), x);
                check(&Nat::from_hex(&hex), x);
                check(&Nat::from_hex(&hex.to_lowercase()), x);
            }
        }
        check(&Nat::from_dec(&"0".repeat(1000)), &Integer::new());
        check(&Nat::from_hex(&"0".repeat(1000)), &Integer::new());
        check(&Nat::from_hex("fF"), &Integer::from(255));
    }

    // `from_dec` of `s` is the number that `rug` reads.
    fn check_from_dec(s: &str) {
        check(&Nat::from_dec(s), &s.parse::<Integer>().unwrap());
    }

    // `n` random decimal digits.
    fn random_digits(rng: &mut Rng, n: usize) -> String {
        (0..n)
            .map(|_| char::from(b'0' + rng.below(10) as u8))
            .collect()
    }

    // `from_dec` of `n` digits for each `n` in `lens`: all nines, 10^(n - 1), all zeros, a one
    // after zeros, ones at both ends, the digits that end in a run of zeros or nines, and
    // random digits.
    fn check_dec_lengths(lens: impl IntoIterator<Item = usize>, rng: &mut Rng) {
        let z = |k: usize| "0".repeat(k);
        for n in lens {
            let half = n / 2;
            let mut cases = vec![
                "9".repeat(n),
                format!("1{}", z(n - 1)),
                z(n),
                format!("{}1", z(n - 1)),
                random_digits(rng, half) + &z(n - half),
                random_digits(rng, half) + &"9".repeat(n - half),
            ];
            if n >= 2 {
                cases.push(format!("1{}1", z(n - 2)));
            }
            for _ in 0..4 {
                cases.push(random_digits(rng, n));
            }
            for s in &cases {
                assert_eq!(s.len(), n);
                check_from_dec(s);
            }
        }
    }

    // Each number of digits up to 80, where `from_dec` takes one limb up to 19 digits, a
    // `u128` up to 38 and then one more chunk of 38 after each multiple of 38.
    #[test]
    fn dec_lengths_of_chunks() {
        check_dec_lengths(1..=80, &mut rng(7));
    }

    // The numbers of digits around `DEC_CUTOFF`, and 10^3, 10^4 and, with optimization, 10^5.
    // From DEC_CUTOFF - 39 to `DEC_CUTOFF`, where `from_dec` reads all the digits 38 at a time,
    // the first chunk of `dec_chunks` takes each length from 0 to 37. Above `DEC_CUTOFF`, it
    // reads the digits after the first ones 19 at a time, and each count of first digits, from
    // DEC_CUTOFF - 18 to DEC_CUTOFF, comes with 1 to 4 chunks of 19 after it.
    #[test]
    fn dec_lengths_across_cutoff() {
        let mut rng = rng(9);
        let t = DEC_CUTOFF;
        check_dec_lengths((t - 39..=t + 77).chain([t + 380, t + 381]), &mut rng);
        check_dec_lengths([1000, 10_000], &mut rng);
        if !cfg!(debug_assertions) {
            check_dec_lengths([100_000], &mut rng);
        }
    }

    // Random digits with a run of zeros or of nines that ends, starts or lies across the point
    // where `from_dec` goes from 38 digits at a time to 19, or that covers all the digits before
    // or after it, so that the number it has read at that point is 0, or the digits after it
    // are all 0 or all 9.
    #[test]
    fn dec_runs_across_cutoff() {
        let mut rng = rng(10);
        for n in [
            DEC_CUTOFF + 1,
            DEC_CUTOFF + 19,
            DEC_CUTOFF + 20,
            3 * DEC_CUTOFF + 7,
        ] {
            // Where the digits read 19 at a time begin.
            let p = n - (n - DEC_CUTOFF).div_ceil(19) * 19;
            let runs = [1, 19, 38, 400]
                .into_iter()
                .flat_map(|w| [(p - w, p), (p, p + w), (p - w, p + w)])
                .chain([(0, p), (p, n)])
                .map(|(a, b)| (a, b.min(n)));
            for (a, b) in runs {
                for d in *b"09" {
                    let mut s = random_digits(&mut rng, n).into_bytes();
                    s[a..b].fill(d);
                    check_from_dec(std::str::from_utf8(&s).unwrap());
                }
            }
        }
    }

    // Up to 3 times `DEC_CUTOFF` decimal digits and at most 599 more, in runs of up to 600
    // zeros, nines and random digits, so that whole chunks of 19 or 38 digits are often all 0
    // or all 9.
    #[test]
    fn dec_long_digit_runs() {
        let n = n_cases() / 50;
        let mut rng = rng(11);
        for _ in 0..n {
            let len = 1 + rng.below(3 * DEC_CUTOFF as u64) as usize;
            check_from_dec(&digit_runs(&mut rng, len, 600));
        }
        eprintln!("nat dec long digit runs: {} cases", n);
    }

    // `mul_add_u128` against `rug` on the patterns, at the ends of its bounds `m < 2^127` and
    // `c < 2^127`: the carry is below 2^127, and the limbs and the carry are `x * m + c`.
    #[test]
    fn mul_add_u128_against_rug() {
        let top = (1u128 << 127) - 1;
        let ms = [1, 10, TEN38, top, 1 << 64, (1 << 64) - 1, 1 << 126 | 1];
        let cs = [0, 1, TEN38 - 1, top, 1 << 64, u128::from(u64::MAX)];
        for x in patterns() {
            for &m in &ms {
                for &c in &cs {
                    let mut v = x.0.clone();
                    let carry = mul_add_u128(&mut v, m, c);
                    assert!(carry <= top);
                    let want = int(&x) * Integer::from(m) + Integer::from(c);
                    let got = Integer::from_digits(&v, Order::Lsf)
                        + (Integer::from(carry) << (64 * v.len() as u32));
                    assert_eq!(got, want, "{:?} {} {}", x, m, c);
                }
            }
        }
    }

    #[test]
    fn dec_of_patterns() {
        let t = 10u64.pow(19);
        for x in [0, 1, 9, 10, t / 10, t - 1, t, t + 1, u64::MAX] {
            check_dec(&Nat::from_u64(x));
        }
        // The patterns and their products, which have runs of all-ones limbs.
        let p = patterns();
        for x in &p {
            check_dec(x);
            for y in &p {
                check_dec(&(x * y));
            }
        }
    }

    // `div_ten19` against the division of `u128`s, at the edges of each limb and at random
    // limbs, with `u1 < 10^19`.
    #[test]
    fn div_ten19_against_u128() {
        let d = TEN19;
        let check = |u1: u64, u0: u64| {
            let u = u128::from(u1) << 64 | u128::from(u0);
            let q = u / u128::from(d);
            let r = u % u128::from(d);
            assert_eq!(div_ten19(u1, u0), (q as u64, r as u64), "{} {}", u1, u0);
        };
        let edges = [0, 1, d - 1, d, d + 1, 1 << 63, u64::MAX - 1, u64::MAX];
        for u1 in [0, 1, 2, d / 2, d - 2, d - 1] {
            for u0 in edges {
                check(u1, u0);
            }
        }
        // Three that take the second correction, the last one after the first. About 1 in
        // 37,000 of the random pairs `(rng.below(d), rng.next())` below take it.
        check(9_443_391_404_544_877_980, 18_434_464_838_440_772_485);
        check(9_996_495_421_046_545_653, 18_150_718_620_628_027_899);
        check(9_878_688_000_699_061_400, 18_163_098_614_498_518_574);
        let mut rng = rng(6);
        for _ in 0..n_cases() * 100 {
            check(rng.below(d), rng.next());
            // The remainder `d - 1` from the limb above.
            check(d - 1, rng.next());
        }
    }

    // `top_digits` and `write_digits` against the `Display` of `u64`, and `to_dec` of one limb:
    // at 0, 9, 10, 99, 100, at 10^k - 1, 10^k and 10^k + 1, at u64::MAX and at random numbers
    // of each count of digits from 1 to 20, with `write_digits` at every length from that
    // count to 20.
    #[test]
    fn digit_writers_against_display() {
        let mut xs = vec![0, 9, 10, 99, 100, TEN19 - 1, u64::MAX - 1, u64::MAX];
        for k in 0..=19 {
            let p = 10u64.pow(k);
            xs.extend([p - 1, p, p + 1]);
        }
        let mut rng = rng(7);
        for k in 1..=20 {
            // [10^(k - 1), 10^k), or [10^19, 2^64 - 1) for k = 20.
            let lo = 10u64.pow(k - 1);
            let hi = 10u64.checked_pow(k).unwrap_or(u64::MAX);
            for _ in 0..n_cases() / 10 {
                xs.push(lo + rng.below(hi - lo));
            }
        }
        for &x in &xs {
            let s = x.to_string();
            let (d, n) = top_digits(x);
            assert_eq!(&d[20 - n..], s.as_bytes(), "{}", x);
            for w in s.len()..=20 {
                let mut out = vec![0; w];
                write_digits(&mut out, x);
                assert_eq!(out, format!("{:0w$}", x).as_bytes(), "{} {}", x, w);
            }
            check_dec(&Nat::from_u64(x));
        }
    }

    // 2^(64 n) - 1, 2^(64 n) and 2^(64 n) + 1, the largest number of `n` limbs and the smallest
    // two of `n + 1`, for each `n` up to 41, one limb more than `src/format.rs` prints.
    #[test]
    fn dec_all_ones_limbs() {
        let one = Nat::from_u64(1);
        for n in 1..=41 {
            let x = Nat::from_limbs(vec![u64::MAX; n]);
            check_dec(&x);
            check_dec(&(&x + &one));
            check_dec(&(&(&x + &one) + &one));
        }
    }

    // 10^k - 1, 10^k and 10^k + 1 for each k up to 1100. Where the number of digits passes a
    // multiple of 19 (k = 18, 19, 20, 38, 39, 57, ...), `to_dec` takes one more chunk of 19
    // digits, and its last chunks are all 9 or all 0.
    #[test]
    fn dec_around_powers_of_ten() {
        let one = Nat::from_u64(1);
        for k in 0..=1100u32 {
            let p = pow10(k);
            check(&p, &Integer::from(Integer::u_pow_u(10, k)));
            check_dec(&(&p - &one));
            check_dec(&p);
            check_dec(&(&p + &one));
        }
    }

    // 2^k - 1, 2^k and 2^k + 1, the smallest and the largest numbers of k + 1 bits and the
    // number after 2^k, up to 100,000 bits: `to_dec` of numbers far longer than the bounds that
    // `src/format.rs` prints.
    #[test]
    fn dec_around_powers_of_two() {
        let one = Nat::from_u64(1);
        for k in (0..=2100).chain([4095, 4096, 4097, 99_999, 100_000]) {
            let p = &one << k;
            check_dec(&(&p - &one));
            check_dec(&p);
            check_dec(&(&p + &one));
        }
    }

    // c * 10^(19j) + r, whose chunks of 19 digits between the top and the last are all 0, and
    // 10^(19j) + 10^(19i) for i < j, a 1 at the end of a chunk among chunks of zeros. `to_dec`
    // prints each chunk of zeros as 19 zeros.
    #[test]
    fn dec_zero_chunks() {
        let t = 10u64.pow(19);
        let p: Vec<Nat> = (0..=60).map(|j| pow10(19 * j)).collect();
        for (j, pj) in p.iter().enumerate() {
            for c in [1, 7, t / 10, t - 1, t, u64::MAX] {
                let top = pj * &Nat::from_u64(c);
                for r in [0, 1, t / 10, t - 1] {
                    check_dec(&(&top + &Nat::from_u64(r)));
                }
            }
            for pi in &p[..j] {
                check_dec(&(pj + pi));
            }
        }
    }

    // At least `len` decimal digits, in runs of 1 to `max` zeros, nines or random digits.
    fn digit_runs(rng: &mut Rng, len: usize, max: u64) -> String {
        let mut s = String::with_capacity(len + max as usize);
        while s.len() < len {
            let kind = rng.below(3);
            for _ in 0..1 + rng.below(max) {
                s.push(match kind {
                    0 => '0',
                    1 => '9',
                    _ => char::from(b'0' + rng.below(10) as u8),
                });
            }
        }
        s
    }

    // Up to about 1200 decimal digits in runs of zeros, nines and random digits, so that whole
    // chunks of 19 digits are often all 0 or all 9, read by `from_dec` and printed back by
    // `to_dec`.
    #[test]
    fn dec_random_digit_runs() {
        let n = n_cases();
        let mut rng = rng(5);
        for _ in 0..n {
            let len = 1 + rng.below(1200) as usize;
            let s = digit_runs(&mut rng, len, 40);
            let x = Nat::from_dec(&s);
            check_dec(&x);
            let digits = s.trim_start_matches('0');
            assert_eq!(x.to_dec(), if digits.is_empty() { "0" } else { digits });
        }
        eprintln!("nat dec digit runs: {} cases", n);
    }

    // Divisions in which the estimate of a quotient limb after D3 is 1 too large, so that D6
    // adds the divisor back: for `v = w * B^(n - 2) + low` with `w` of 2 limbs, its top limb
    // at least B/2, and `0 < low < B^(n - 2)`, and a `u = q0 * w * B^(n - 2)` with
    // `1 < q0 < B`, D3 estimates `q0` from the top three limbs of `u` and the top two of `v`,
    // but `u / v = q0 - q0 * low / v`, and `0 < q0 * low < v`, so the quotient is `q0 - 1`.
    // For `q0 = 1`, also tested, `u < v`, which `div_rem` answers before Algorithm D.
    // Shifting both right by `s` bits that are 0 makes D1 shift them back. The same divisions
    // above `j` zero limbs, u * B^j + s0 by v * B^j for s0 < B^j, which `div_rem` strips from
    // the divisor, add back too, and have the remainder r * B^j + s0.
    #[test]
    fn div_rem_add_back() {
        let mut rng = rng(2);
        let h = 1 << 63;
        for n in 3..=6 {
            for s in [0, 1, 32, 63] {
                for (w0, w1) in [(0, h), (u64::MAX, u64::MAX), (rng.next(), rng.next() | h)] {
                    for q0 in [1, 2, u64::MAX, rng.next() | 1] {
                        let mut low: Vec<u64> = (0..n - 2).map(|_| rng.limb()).collect();
                        low[0] = ((rng.next() | h) >> s) << s;
                        let mut v = low;
                        v.extend([w0, w1]);
                        let mut w = vec![0; n - 2];
                        w.extend([w0, w1]);
                        let v = int(&Nat::from_limbs(v)) >> s;
                        let u = (int(&Nat::from_limbs(w)) * q0) >> s;
                        let (q, r) = nat(&u).div_rem(&nat(&v));
                        let (qq, rr) = u.clone().div_rem_floor(v.clone());
                        assert_eq!(qq, q0 - 1);
                        check(&q, &qq);
                        check(&r, &rr);
                        for j in [1, 2] {
                            let s0 = int(&Nat::from_limbs((0..j).map(|_| rng.limb()).collect()));
                            let b = 64 * j as u32;
                            let x = nat(&(Integer::from(&u << b) + &s0));
                            let (q, r) = x.div_rem(&nat(&Integer::from(&v << b)));
                            check(&q, &qq);
                            check(&r, &(Integer::from(&rr << b) + &s0));
                        }
                    }
                }
            }
        }
    }

    // Divisors with 0 to 79 zero limbs at the bottom, which `div_rem` strips: c * 2^t for an
    // odd limb c and t = 64 * i + 0, 1, 62 or 63 for i from 0 to 79, so that 2^t, such as
    // `scale` in `src/parse.rs` divides by, has 1 to 80 limbs, with dividends around them, of
    // up to 3 limbs more, and with quotients of up to 4 limbs.
    #[test]
    fn div_rem_low_zero_limbs() {
        let mut rng = rng(4);
        for limbs in 1..=80u32 {
            for bit in [0, 1, 62, 63] {
                let t = 64 * (limbs - 1) + bit;
                for c in [1, 3, 1 << 63 | 1, u64::MAX, rng.next() | 1] {
                    let d = Integer::from(c) << t;
                    let mut xs = vec![
                        Integer::from(&d - 1u32),
                        d.clone(),
                        Integer::from(&d + 1u32),
                        Integer::from(&d << 64u32) - 1u32,
                    ];
                    for _ in 0..4 {
                        let q = int(&rng.nat(3));
                        let r = int(&rng.nat(u64::from(limbs) + 1)) % &d;
                        xs.push(q * &d + r);
                        xs.push(int(&rng.nat(u64::from(limbs) + 3)));
                    }
                    for x in &xs {
                        let (q, r) = nat(x).div_rem(&nat(&d));
                        let (qq, rr) = x.clone().div_rem_floor(d.clone());
                        check(&q, &qq);
                        check(&r, &rr);
                    }
                }
            }
        }
    }

    #[test]
    fn random() {
        let n = n_cases();
        let mut rng = rng(3);
        for _ in 0..n {
            let x = rng.nat(80);
            let y = rng.nat(80);
            let s = [rng.below(200), rng.below(1 << 16)];
            check_ops(&x, &y, &s);
            let [dec, hex] = digit_strings(&int(&x), rng.below(40) as usize);
            check(&Nat::from_dec(&dec), &int(&x));
            check(&Nat::from_hex(&hex), &int(&x));
            check_dec(&x);
        }
        eprintln!("nat random: {} cases", n);
    }
}

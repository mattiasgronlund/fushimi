# The aarch64 backend against `force-generic` on an Apple M1 Pro, at `7d80003`

The raw results of issue #3: inari's default aarch64 backend, which switches the
rounding mode around every directed-rounding instruction (`impl_op_round!` in
`src/simd/aarch64.rs`), against the portable backend (`--features
force-generic`). Measured on 2026-11-14. This branch is `7d80003` with this
directory added; nothing in inari changed.

## Setup

- Apple M1 Pro (10 cores), 32 GB, on its power adapter, Low Power Mode off
  (`pmset -g`: `lowpowermode 0`).
- macOS 26.6.2 (25G83).
- rustc 1.101.0-nightly (c980177d8 2026-11-06), the default toolchain on this
  machine; the repository pins none.
- criterion 0.7.0 (from `bench/Cargo.lock`), `lto = "fat"`, `codegen-units = 1`
  (the package's `[profile.bench]`), no `RUSTFLAGS`.
- macOS has no `taskset`, so nothing was pinned to a core. The other Claude
  session on this machine (solidcore's) held its builds and timed runs for the
  whole benchmark window.

## Step 1: tests

Run in the repository root, natively, as `.github/workflows/ci-aarch64.yml`
runs them, with `CARGO_BUILD_JOBS=5 RUST_TEST_THREADS=5`:

```bash
cargo test --release
cargo test --release --features force-generic
```

Both pass: per build, 340 unit tests (5 ignored), 210 in `itf1788`, 2 in
`macros`, 1 in `model_constants` and 40 doctests (2 ignored). The logs are
`logs/test-aarch64.log` and `logs/test-generic.log`.

The tests link MPFR through `rug` and `gmp-mpfr-sys` 1.7.1 with no workaround.
`cargo +1.99.1 test --release`, the toolchain of solidcore's session, also links
and passes (`logs/test-aarch64-rustc-1.99.1.log`). `gmp-mpfr-sys` reused its
cache in `~/Library/Caches/gmp-mpfr-sys/1.7` here, so these builds did not
compile GMP and MPFR from scratch. solidcore's failing link ("builds GMP and
MPFR for macOS 26.0, and the link targets 11.0") came from a fresh build of
them, with `lto = "fat"` and `codegen-units = 1`.

## Step 2: benchmarks

In `bench/`, each configuration has its own target directory, built beforehand
so that no build ran right before a timing:

```bash
cd bench
CARGO_TARGET_DIR=target-aarch64 cargo bench --no-run --bench primitives --bench intervals
CARGO_TARGET_DIR=target-generic cargo bench --no-run --features force-generic --bench primitives --bench intervals
../experiments/aarch64-baseline-m1/run-all.sh
ROUNDS="aarch64:3 generic:3" ../experiments/aarch64-baseline-m1/run-all.sh
ROUNDS="aarch64:4 generic:4" ../experiments/aarch64-baseline-m1/run-all.sh
```

`run.sh <config> <round>` runs one round:
`cargo bench [--features force-generic] --bench primitives --bench intervals -- --save-baseline <config>-r<round>`.
It logs the load average before and after to `loadavg.log`, and copies every
benchmark's `estimates.json` to `criterion/<config>-r<round>/<benchmark>/`.
`run-all.sh` runs the rounds in order, each once the one-minute load average is
below 2.5, and saves the busiest processes at its start to `logs/ps-*.txt`.
`tables.py` prints the tables of the issue comment (`tables.md`) from
`criterion/`.

**Rounds.** The order was `aarch64-r1`, `generic-r1`, `aarch64-r2`,
`generic-r2`, then, after a break, `aarch64-r3`, `generic-r3`, `aarch64-r4`,
`generic-r4`. Safari and Activity Monitor were quit before round 3. Three runs
were dropped and moved to `dropped/`, as `loadavg.log` records:
- a first `aarch64-r1`, which started at a load average of 4.8, right after the
  builds and with Activity Monitor open, and was run again;
- `generic-r1`, which started with a Safari web content process at 87% CPU. Its
  `div` rows were 3–4% slower than `generic-r2`'s;
- `aarch64-r3`, which started with `opendirectoryd` at 26% and `assistantd` at
  18% CPU. Six of its `mul` and `mul_tiny` rows were 3–4% slower than the other
  aarch64 rounds'.

So the tables use `aarch64-r1`, `-r2` and `-r4`, and `generic-r2`, `-r3` and
`-r4`. The aarch64 rounds agree to within 0.5% on every row. Five generic rows
spread by 3–5%: `div/PP`, `div/PN`, `sqrt/M`, `mul_add_ru/throughput` and the
3×3 determinant. The slow round is a different one from row to row, and none
of them started under load, so this looks like the per-process variation
BENCHMARKS.md's "Variance" describes on x86-64, not load. More rounds were not
run. Taking the median of the rounds instead of the lowest changes no
`generic / aarch64` ratio by more than 0.01.

On an idle M1 Pro, macOS reports a one-minute load average of about 2.3, which
is the floor of every kept run.

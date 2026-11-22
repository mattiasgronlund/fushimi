# The aarch64 backend without FPCR writes, timed on an Apple M1 Pro (issue #6)

The raw files of issue #6: `6633461`'s aarch64 backend against both builds of
`9577556`, and four variants of its `mul_add_ru`. The results are in the issue's
comment; `out/tables.md` holds the tables as `tables/` printed them.

## Setup

- Apple M1 Pro (10 cores), macOS 26.6.2, on its power adapter, Low Power Mode off.
- `rustc 1.101.0-nightly (c980177d8 2026-11-06)`, no `RUSTFLAGS` (the repo's
  `.cargo/config.toml` passes `-Ctarget-cpu=native`).
- criterion 0.7.0, from issue #3's `bench/Cargo.lock`, copied into every checkout.

| Checkout | Commit | `git status --short` |
|---|---|---|
| `inari-base` | `957755612a93f62dc05748f972596a7136058632` | `M bench/benches/intervals.rs`, `M bench/benches/primitives.rs` (`6633461`'s two bench files) |
| `inari-neon` | `66334615ec9e9a0b6439af1d87b2c809ac76aeb5` | clean |
| `inari-V1` | `6633461` + `variants/V1.patch` | `M src/simd/aarch64.rs`, `M src/simd/aarch64/fma.rs` |
| `inari-V24` | `6633461` + `variants/V24.patch` | `M src/simd/aarch64/fma.rs` |
| `inari-V6s` | `6633461` + `variants/V6s.patch` | `M src/simd/aarch64/fma.rs`, `M src/simd/aarch64/lanewise.rs` |
| `inari-V246s` | `6633461` + `variants/V246s.patch` | `M src/simd/aarch64/fma.rs`, `M src/simd/aarch64/lanewise.rs` |

## Commands

- `tests.sh`: step 1 of the issue. Its outputs are in `tests/`.
- `bench.sh`: the issue's script, with two additions. It keeps the Mac awake with
  `caffeinate -i -s`, and each run waits until the 1-minute load average is below
  2.5 and no process is above 15 % CPU (issue #7's rule). Run from the directory that
  holds the checkouts (it writes to `out6/`, renamed `out/` here), first as `zsh bench.sh build`, then as
  `ROUNDS="1 2" zsh bench.sh` and `ROUNDS="3 4 5" zsh bench.sh`.
  - A first attempt at rounds 1 and 2 passed `ROUNDS` in a way zsh doesn't split
    into words, so its first run was named `fpcr-r1 2`. It was stopped before its
    first estimate; `out/loadavg-aborted-word-split.log` is its only trace.
- `tables/`: a Rust program that prints the tables from the baselines:
  ```
  cargo run --release --manifest-path tables/Cargo.toml -- criterion out/neon-r1.txt \
    --prev <issue #4's CRITERION_HOME> aarch64-r1,aarch64-r2,aarch64-r4,generic-r2,generic-r4,generic-r5,proto-r2,proto-r4,proto-r5
  ```
  `--prev` needs issue #4's baselines with their `benchmark.json`, which the
  `exp/aarch64-proto-m1` branch doesn't hold. Without it, the program prints only
  the three tables.

## Files

- `criterion/<benchmark>/<baseline>/`: `estimates.json`, `sample.json` and
  `benchmark.json` of every benchmark and round. No round was dropped.
- `out/<baseline>.txt`: criterion's output of every run; `out/build-*.txt`: the
  `--no-run` builds; `out/loadavg.log`: the load average before and after each run.
- `tests/`: the full output of every test run of step 1.

# The aarch64 prototype against `7d80003` on an Apple M1 Pro

Raw files of issue #4: the prototype of `exp/aarch64-round-proto`, which rounds
without writing FPCR, timed against the aarch64 backend and `--features
force-generic` of `7d80003`, in one session (2026-11-15).

## Checkouts
- `inari-7d80003`: `7d800030edfbc1d65974aec9f0ee3d0791fa8d03`, for `aarch64` and `generic`.
- `inari-proto`: `7e31d1bb0e807870da3c7d9899b84d99060e1ffc`, for `proto`.

Both have the `bench/Cargo.lock` of issue #3 (`exp/aarch64-baseline-m1`).

## Setup
- Apple M1 Pro (10 cores), 32 GB, on its power adapter, Low Power Mode off.
- macOS 26.6.2 (25G83), rustc 1.101.0-nightly (c980177d8 2026-11-06), criterion 0.7.0.
- No `RUSTFLAGS`: the repo's `.cargo/config.toml` passes `-Ctarget-cpu=native`.
  The bench profile has `lto = "fat"` and `codegen-units = 1`.
- solidcore's macOS session held its builds and timed runs from the builds to
  the end of round 5.

## Commands
Tests, in `inari-proto`, with `CARGO_BUILD_JOBS=5 RUST_TEST_THREADS=5`
(`logs/test-*.txt`):
```bash
cargo test --release
cargo test --release --features force-generic
INARI_DIFF_N=10000000 cargo test --release --lib simd::differential_tests -- --nocapture
```
Benchmarks: `bench.sh`, run from the directory that holds both checkouts, with
`CRITERION_HOME=$PWD/criterion-aarch64-proto-m1` (empty at the start).
`bench.sh build` builds the three configurations with `--no-run`
(`logs/build.txt`), and `bench.sh rounds <k>...` runs `aarch64-rK`,
`generic-rK` and `proto-rK` for each `k`. From round 3 on, each run waits
until the 1-minute load average is below 2.5, and saves the busiest processes
to `load/ps-<baseline>.txt`. Before round 1 it waited once, and saved
`load/ps-aarch64-r1.txt`.

## Files
- `criterion/<benchmark>/<baseline>/estimates.json`: every round, dropped ones included.
- `loadavg.log`: `sysctl -n vm.loadavg` before and after every run. Its
  `exit` field is not the bench's exit status. The bench logs show that every
  run finished.
- `logs/`: the test, build and bench output.
- `tables.py`, `tables.md`: the tables over the kept rounds, made with
  `python3 tables.py criterion generic-r1 proto-r1 aarch64-r3 generic-r3 proto-r3 aarch64-r5`.

## Dropped rounds
- `generic-r1`: the load average rose to 7.05 during it, and it is the slow
  round of every generic row over 3%.
- `proto-r1`: it started at that load average of 7.05.
- `aarch64-r3`, `generic-r3`, `proto-r3`: macOS background processes were busy
  when they started (`launchd` 44% and `systemstats` 42%; `XProtectRemediatorAdload`
  71%; `opendirectoryd` 57% and `assistantd` 43%).
- `aarch64-r5`: my own disassembly comparison (below) ran during it.

Kept: `aarch64` r1, r2, r4; `generic` r2, r4, r5; `proto` r2, r4, r5.

## The generic `div` rows
The generic interval `div` rows are 6–21% slower than in issue #3, and spread by
up to 13% between quiet rounds. This build's generic `intervals` binary has the
same `__text` size as issue #3's (1 281 760 bytes). Apart from crate hashes in
symbol names and page addresses, about 80 instructions differ.

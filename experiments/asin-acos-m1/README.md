# Timing `asin`, `acos` and the operators on an Apple M1 Pro (issue #5)

Raw files of issue #5: part A (`asin` and `acos`, `7e92e46` against `daa51d1`) and part B
(the operators of `Interval`, `b5dd856` against `7e92e46`, default build and `force-generic`).

## Setup

- **Machine:** Apple M1 Pro (10 cores), 32 GB, on its power adapter, Low Power Mode off.
- **Software:** macOS 26.6.2 (25G83), rustc 1.101.0-nightly (c980177d8 2026-11-06),
  criterion 0.7.0 (the `bench/Cargo.lock` of issue #3's checkout, copied into all three).
  No `RUSTFLAGS`: the repository's `.cargo/config.toml` passes `-Ctarget-cpu=native`.
- **Checkouts:**
  - `inari-asin-7e92e46`: `5da537114ef3a8c73b51ac57c68ed7dc6ff3f398`
    (`origin/exp/asin-acos-bench-7e92e46`; against `7e92e46` only `bench/Cargo.toml` and
    `bench/benches/asin_acos.rs` differ);
  - `inari-asin-daa51d1`: `09d0399249d83522b0695b502b650766e158766d`
    (`origin/exp/asin-acos-bench-daa51d1`; the same two files differ from `daa51d1`);
  - `inari-b5dd856`: `b5dd856f8f6b4c66c9a837beea192d49dcc2f92f`.
- **Arguments of A:** not in this branch. solidcore's
  `experiments/inari-cr-macos-ed65e20/results/acos-args.tsv` at
  `860ef1fde526f0bd7ec81b232729739b93359eb9` of github.com/mattiasgronlund/solidcore,
  42,020 lines, SHA-256 `fcd15ecfa80d6a115184eaad3c7a3feb536e95d7f3b6f96358b330d266083359`,
  passed to the bench through `INARI_ACOS_ARGS`.
- **Isolation:** nothing pinned (macOS has no `taskset`). solidcore's macOS session ran
  nothing timed in the window.

## Files

- `criterion/<benchmark>/<baseline>/estimates.json`: criterion's estimates of every
  benchmark and round, dropped rounds included, in `$CRITERION_HOME`'s layout.
- `out/loadavg.log`: `sysctl -n vm.loadavg` before and after every run.
- `out/<baseline>.txt`: criterion's output of every run; `out/<baseline>.ps.txt`: the five
  busiest processes when the run started; `out/build-*.txt`: the `--no-run` builds.
- `scripts/`: `common.sh` (the `cb`, `idle` and `run` functions of the issue), `a.sh`,
  `a2.sh` and `b.sh` (the drivers), `table_a.py` and `table_b.py` (the tables of the
  comments). Run them from `asin-acos-m1/`, a directory next to the checkouts.

## Part A

Commands, in `bench/` of each checkout, with `INARI_ACOS_ARGS` set:
`cargo bench --bench asin_acos -- --save-baseline asin-<commit>-rK`, interleaved
`7e92e46`, `daa51d1`, round by round. Each run started once the 1-minute load average was
below 2.5 (from round 4 on, also once no other process was above 15% CPU).

- **Kept:** `asin-7e92e46` r1, r2, r4, r5; `asin-daa51d1` r1, r4, r5.
- **Dropped:**
  - `asin-daa51d1-r2`: OneDrive and `fileproviderd` began a sync during it (about 180%
    CPU together, with Spotlight); the load average was 6.2 at its end, and it is 3–7%
    slower than r1 on most series after the first few.
  - `asin-7e92e46-r3`: started on the load average alone while OneDrive was still at
    100% CPU; it is 3.0% slower than r1 on every series, uniformly.
  - `asin-daa51d1-r3`: never ran. The drivers were stopped before it started, and the idle
    test was tightened to also wait for every other process to be below 15% CPU.
- **Spread over 3%:** only `cal` rows, whose iteration is 4,096 calls: `libm_asin/cal`
  (18%), `libm_acos/cal` (16%), `acos_rd/cal` (5.6%), `acos_ru/cal` (3.1%). The libm rows
  take one of two levels per process (`libm_asin/cal`: 5.46–5.75 or 5.96–6.46 ns) in
  rounds that started idle, so more rounds don't narrow them; each cell is the lowest median.

Table: `python3 -I scripts/table_a.py criterion r1,r2,r4,r5 r1,r4,r5`.

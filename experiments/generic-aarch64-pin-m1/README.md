# The `inline(never)` pin of the portable backend on aarch64, timed on an Apple M1 Pro (issue #7)

The raw files of issue #7: `force-generic` builds of `b5dd856` (P0, before the pin),
`2ab7964` (B, with it) and `27b52bb` (A1, without it on aarch64), each at two
layouts. The results are in the issue's comment; `out/tables.md` holds the tables
as `tables/` printed them.

## Setup

- Apple M1 Pro (10 cores), macOS 26.6.2, on its power adapter, Low Power Mode off,
  lid open, kept awake with `caffeinate -i -s`.
- `rustc 1.101.0-nightly (c980177d8 2026-11-06)`; `objdump`: Apple LLVM version 21.0.0.
- criterion 0.7.0, from issue #3's `bench/Cargo.lock` (copied from issue #5's
  `inari-b5dd856` checkout into all three).

| Checkout | Commit | `git status --short` |
|---|---|---|
| `inari-146-P0` | `b5dd856f8f6b4c66c9a837beea192d49dcc2f92f` | clean |
| `inari-146-B` | `2ab79641580ecd1b9ac861629e1e5aed512d9e68` | clean |
| `inari-146-A1` | `27b52bb97da4097bfad4ba61c3079b1ac990d5f6` | clean |

## Commands

From the directory that holds the checkouts:
- `zsh run.sh build`, then `zsh asm-check.sh | tee out/asm-check.txt`, then
  `zsh run.sh` (rounds 1–3, and the `token/*` rounds 1 and 2), then `zsh run-r45.sh`
  (rounds 4 and 5 of the filtered series). `run.sh` is the issue's script, and
  `run-r45.sh` the same with `for k in 4 5; do`.
  - Both write to `out7/`, not `out/`, since `out/` there still held issue #4's
    files. Here it is `out/` again.
- `out/asm-B-trampolines.txt` is the issue's `objdump … | grep -A8` of B's three
  `__bench` functions, at both layouts.
- `tables/`: a Rust program that prints the tables, applies the rule for disturbed
  rounds, and lists the moves:
  ```
  cargo run --release --manifest-path tables/Cargo.toml -- criterion \
    out/B-L0-r1.txt out/token-B-L0-r1.txt tables/issue5-generic.tsv
  ```
  `tables/issue5-generic.tsv` is issue #5's column `generic 7e92e46 / b5dd856`
  (id, ratio, spread), taken from its results comment.

## Files

- `criterion/<benchmark>/<baseline>/`: `estimates.json`, `sample.json` and
  `benchmark.json` of every series and round. No round was dropped for load or sleep.
- `out/<baseline>.txt`: criterion's output of every run; `out/build-*.txt`: the builds, as the last run of `run-r45.sh` rewrote them (each lists its executables, with no `Compiling` line, so no build changed between rounds);
  `out/loadavg.log`: the load average before and after each run.

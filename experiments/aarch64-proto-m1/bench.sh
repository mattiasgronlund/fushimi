#!/bin/zsh
# Issue #4, step 2. Run from the directory that holds the two checkouts.
# Usage: out/bench.sh build | out/bench.sh rounds <k>...
unset RUSTFLAGS
export CRITERION_HOME="$PWD/criterion-aarch64-proto-m1"
mkdir -p "$CRITERION_HOME" out
bench() {  # bench <checkout> <cargo bench options>: the two benches in <checkout>/bench
  local dir=$1; shift
  (cd "$dir/bench" && cargo bench --bench primitives --bench intervals "$@")
}
run() {  # run <checkout> <baseline> [cargo options]
  local dir=$1 base=$2; shift 2
  until [ "$(sysctl -n vm.loadavg | awk '{print ($2 < 2.5)}')" = 1 ]; do sleep 15; done
  ps -Ao pcpu,comm -r | head -6 > "out/ps-$base.txt"
  echo "$base before $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> out/loadavg.log
  bench "$dir" "$@" -- --save-baseline "$base" > "out/$base.txt" 2>&1
  echo "$base after  $(date -u +%FT%TZ) $(sysctl -n vm.loadavg) exit $?" >> out/loadavg.log
}
case $1 in
build)
  export CARGO_BUILD_JOBS=5
  bench inari-7d80003 --no-run
  bench inari-7d80003 --no-run --features force-generic
  bench inari-proto --no-run
  ;;
rounds)
  shift
  for k in "$@"; do
    run inari-7d80003 "aarch64-r$k"
    run inari-7d80003 "generic-r$k" --features force-generic
    run inari-proto "proto-r$k"
  done
  ;;
esac

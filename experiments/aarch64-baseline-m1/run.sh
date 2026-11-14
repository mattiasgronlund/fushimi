#!/bin/sh
# Runs one benchmark round of issue #3: `run.sh <config> <round>`, where
# <config> is `aarch64` or `generic`. Run from `bench/`. Each configuration has
# its own target directory, built beforehand with `cargo bench --no-run`, so
# that no build runs right before the timing.
set -eu
config=$1
round=$2
baseline=$config-r$round
out=../experiments/aarch64-baseline-m1
features=
if [ "$config" = generic ]; then features="--features force-generic"; fi

echo "$baseline before $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> $out/loadavg.log
# shellcheck disable=SC2086
CARGO_TARGET_DIR=target-$config cargo bench $features --bench primitives --bench intervals \
  -- --save-baseline "$baseline" > "$out/logs/bench-$baseline.log" 2>&1
echo "$baseline after  $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> $out/loadavg.log

# Keep each benchmark's estimates.json, under criterion/<baseline>/<benchmark>/.
cd target-$config/criterion
find . -path "*/$baseline/estimates.json" | while read -r f; do
  bench=$(dirname "$(dirname "$f")")
  mkdir -p "../../$out/criterion/$baseline/$bench"
  cp "$f" "../../$out/criterion/$baseline/$bench/estimates.json"
done

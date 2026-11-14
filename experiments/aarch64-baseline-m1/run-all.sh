#!/bin/sh
# Runs the four rounds of issue #3 interleaved, each after the one-minute load
# average has dropped below 2.5. Run from `bench/`.
set -eu
for r in ${ROUNDS:-aarch64:1 generic:1 aarch64:2 generic:2}; do
  until [ "$(sysctl -n vm.loadavg | awk '{print ($2 < 2.5)}')" = 1 ]; do sleep 10; done
  ps -Ao pcpu,comm -r | head -6 > "../experiments/aarch64-baseline-m1/logs/ps-${r%%:*}-r${r##*:}.txt"
  ../experiments/aarch64-baseline-m1/run.sh "${r%%:*}" "${r##*:}"
done

# Sourced from ~/git/mattiasgronlund/asin-acos-m1 (zsh or bash).
export CRITERION_HOME="$PWD/criterion-asin-acos-m1"
export INARI_ACOS_ARGS="$PWD/acos-args.tsv"
unset RUSTFLAGS
cb() {  # cb <checkout> <cargo bench arguments>: cargo bench in <checkout>/bench
  local dir=$1; shift
  (cd "../$dir/bench" && cargo bench "$@")
}
busy() {  # the busiest other process above 15% CPU, if any
  ps -Ao pcpu,comm -r | awk 'NR > 1 && $1 > 15 && $0 !~ /claude|ps$/ {print; exit}'
}
idle() {  # wait until the 1-minute load average is below 2.5 and no other process is above 15% CPU
  while [ "$(sysctl -n vm.loadavg | awk '{print ($2 < 2.5)}')" != 1 ] || [ -n "$(busy)" ]; do sleep 30; done
}
run() {  # run <checkout> <baseline> <cargo bench arguments, up to and with --> [filter]
  local dir=$1 base=$2; shift 2
  idle
  echo "$base before $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> out/loadavg.log
  ps -Ao pcpu,comm -r | head -6 > "out/$base.ps.txt"
  cb "$dir" "$@" --save-baseline "$base" > "out/$base.txt" 2>&1
  echo "$base after  $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> out/loadavg.log
}

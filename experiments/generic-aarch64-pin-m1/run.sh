TOP=$PWD
caffeinate -i -s -w $$ &  # keeps the Mac awake while this shell runs
export CRITERION_HOME="$TOP/criterion-generic-aarch64-pin-m1"  # new and empty
mkdir -p "$CRITERION_HOME" "$TOP/out7"
FILTER='^((add_ru|mul_ru|div_ru|mul_add_ru|sqrt1_ru)/(throughput|latency)/|(add|sub|mul|mul_tiny|div)/|unary/)'
bench() {  # bench <P0|B|A1> <L0|L6> <cargo bench options>: the two benches of inari-146-<checkout>, force-generic
  local side=$1 lay=$2; shift 2
  (
    cd "$TOP/inari-146-$side/bench" || exit 1
    export CARGO_TARGET_DIR="$TOP/target-146/$side-$lay"
    if [ "$lay" = L6 ]; then
      export RUSTFLAGS="-Ctarget-cpu=native -Cllvm-args=-align-all-functions=6"
    else
      unset RUSTFLAGS
    fi
    cargo bench --features force-generic --bench primitives --bench intervals "$@"
  )
}
for l in L0 L6; do
  for s in P0 B A1; do
    bench "$s" "$l" --no-run > "$TOP/out7/build-$s-$l.txt" 2>&1 || echo "build $s-$l failed"
  done
done
if [ "${1-}" = build ]; then exit 0; fi  # `zsh <file> build` stops here, before the rounds
quiet() {  # wait until the 1-minute load average is below 2.5 and no process is above 15 % CPU
  until [ "$(sysctl -n vm.loadavg | awk '{ print ($2 < 2.5) }')" = 1 ] &&
    [ "$(ps -A -o %cpu= | awk '$1 > 15 { n++ } END { print n + 0 }')" = 0 ]; do
    sleep 30
  done
}
run() {  # run <P0|B|A1> <L0|L6> <baseline> <filter>
  local side=$1 lay=$2 base=$3 filter=$4
  quiet
  echo "$base before $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> "$TOP/out7/loadavg.log"
  bench "$side" "$lay" -- --save-baseline "$base" "$filter" > "$TOP/out7/$base.txt" 2>&1
  echo "$base after  $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> "$TOP/out7/loadavg.log"
}
for k in 1 2 3; do
  for l in L0 L6; do
    for s in P0 B A1; do run "$s" "$l" "$s-$l-r$k" "$FILTER"; done
  done
  if [ "$k" -le 2 ]; then
    for l in L0 L6; do
      for s in B A1; do run "$s" "$l" "token-$s-$l-r$k" '^token/'; done
    done
  fi
done

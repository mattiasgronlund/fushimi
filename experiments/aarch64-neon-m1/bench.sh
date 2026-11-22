# Issue #6 runner, from the issue's script; adds caffeinate and #7's process check to quiet().
TOP=$PWD
caffeinate -i -s -w $$ &
export CRITERION_HOME="$TOP/criterion-aarch64-neon-m1"
mkdir -p "$CRITERION_HOME" out6
bench() {
  local dir=$1; shift
  (cd "$dir/bench" && cargo bench --bench primitives --bench intervals "$@")
}
if [ "${1-}" = build ]; then
  bench inari-base --no-run > out6/build-fpcr.txt 2>&1 || echo "build fpcr failed"
  bench inari-base --no-run --features force-generic > out6/build-generic.txt 2>&1 || echo "build generic failed"
  for c in neon V1 V24 V6s V246s; do bench "inari-$c" --no-run > out6/build-$c.txt 2>&1 || echo "build $c failed"; done
  echo BUILT; exit 0
fi
quiet() {
  until [ "$(sysctl -n vm.loadavg | awk '{ print ($2 < 2.5) }')" = 1 ] &&
    [ "$(ps -A -o %cpu= | awk '$1 > 15 { n++ } END { print n + 0 }')" = 0 ]; do sleep 30; done
}
run() {
  local dir=$1 base=$2; shift 2
  local opts=() filter=()
  while [ $# -gt 0 ] && [ "$1" != -- ]; do opts+=("$1"); shift; done
  [ $# -gt 0 ] && shift && filter=("$@")
  quiet
  echo "$base before $(date -u +%FT%TZ) $(sysctl -n vm.loadavg)" >> out6/loadavg.log
  bench "$dir" "${opts[@]}" -- --save-baseline "$base" "${filter[@]}" > "out6/$base.txt" 2>&1; local rc=$?
  echo "$base after  $(date -u +%FT%TZ) $(sysctl -n vm.loadavg) exit $rc" >> out6/loadavg.log
  echo "done $base"
}
for k in $(echo "${ROUNDS:-1 2}"); do
  run inari-base "fpcr-r$k"
  run inari-base "generic-r$k" --features force-generic
  run inari-neon "neon-r$k"
  for v in V1 V24 V6s V246s; do
    run "inari-$v" "$v-r$k" -- '^mul_add|horner8_mul_add'
  done
done
echo ROUNDSDONE

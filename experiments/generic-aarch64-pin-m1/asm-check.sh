# Each cell is <instructions>@<start address mod 64>, without the nop and udf that pad a function's end;
# `missing` if the executable has no function of that name, two cells with a comma if it has two.
TOP=$PWD
P='inari::__bench::add_ru|inari::__bench::mul_ru|inari::__bench::div_ru'
I='<inari::interval::Interval as core::ops::arith::Mul>::mul|inari::simd::generic::mul1_ru_tiny::<true>|<inari::interval::Interval>::sqrt'
fns() {  # fns <executable> <names, separated by |>: one cell per name
  objdump -d -C --no-show-raw-insn "$1" | awk -v names="$2" '
    function fin() { if (cur) { seen[cur]++; got[cur] = (seen[cur] > 1 ? got[cur] "," : "") n "@" a } }
    BEGIN { k = split(names, want, "|"); h = "0123456789abcdef" }
    /^[0-9a-f]+ <.*>:$/ {
      fin(); cur = ""; s = $0; sub(/^[0-9a-f]+ <_?/, "", s); sub(/(::h[0-9a-f]+)?>:$/, "", s)
      for (i = 1; i <= k; i++) if (s == want[i]) cur = i
      a = ((index(h, substr($1, length($1) - 1, 1)) - 1) * 16 + index(h, substr($1, length($1), 1)) - 1) % 64
      n = 0; p = 0; next
    }
    cur && /^ *[0-9a-f]+:/ { if ($0 ~ /:[ \t]+(nop|udf)/) p++; else { n += p + 1; p = 0 } }
    END { fin(); for (i = 1; i <= k; i++) printf " %s", (seen[i] ? got[i] : "missing"); print "" }'
}
exe() { sed -n "s|^ *Executable benches/$3\.rs (\(.*\))\$|\1|p" "$TOP/out7/build-$1-$2.txt"; }
echo 'build  primitives: __bench::add_ru mul_ru div_ru  intervals: Interval::mul mul1_ru_tiny::<true> Interval::sqrt'
for l in L0 L6; do
  for s in P0 B A1; do
    cd "$TOP/inari-146-$s/bench" || exit 1  # cargo names an executable relative to the directory it ran in
    echo "$s-$l  primitives:$(fns "$(exe "$s" "$l" primitives)" "$P")  intervals:$(fns "$(exe "$s" "$l" intervals)" "$I")"
  done
done

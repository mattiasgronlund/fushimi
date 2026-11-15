# Table of part A from $CRITERION_HOME:
#   python3 -I scripts/table_a.py <criterion dir> <7e92e46 rounds, e.g. r1,r2> <daa51d1 rounds>
# Each cell is the lowest median over the kept rounds, in ns per call; spread is the largest
# (max - min) / min over the rounds of one commit in the row.
import json, sys, pathlib

root = pathlib.Path(sys.argv[1])
calls = {"sc": 42020, "cal": 4096}
funcs = ["asin_rn", "asin_rd", "asin_ru", "interval_asin", "libm_asin",
         "acos_rn", "acos_rd", "acos_ru", "interval_acos", "libm_acos"]
commits = ["7e92e46", "daa51d1"]
rounds = dict(zip(commits, (a.split(",") for a in sys.argv[2:4])))

def med(func, s, base):
    p = root / func / s / base / "estimates.json"
    return json.loads(p.read_text())["median"]["point_estimate"] / calls[s]

cell, spread = {}, {}
for f in funcs:
    for s in calls:
        sp = 0.0
        for c in commits:
            v = [med(f, s, f"asin-{c}-{r}") for r in rounds[c]]
            cell[f, s, c] = min(v)
            sp = max(sp, (max(v) - min(v)) / min(v))
            for r, x in zip(rounds[c], v):
                print(f"# {f}/{s} {c} {r} {x:.3f}", file=sys.stderr)
        spread[f, s] = sp

print("| Series | 7e92e46 (ns) | daa51d1 (ns) | daa51d1 / 7e92e46 | daa51d1 / libm | spread |")
print("|---|--:|--:|--:|--:|--:|")
for f in funcs:
    lib = "libm_asin" if "asin" in f else "libm_acos"
    for s in calls:
        a, b = cell[f, s, "7e92e46"], cell[f, s, "daa51d1"]
        print(f"| {f}/{s} | {a:.2f} | {b:.2f} | {b/a:.3f}× | {b/cell[lib, s, 'daa51d1']:.2f}× | {spread[f, s]*100:.1f}% |")

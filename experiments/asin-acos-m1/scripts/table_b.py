# Tables of part B: python3 -I scripts/table_b.py <criterion dir> [baselines to drop...]
# Each cell is the lowest median over the kept rounds per operation (N = 1024 per
# iteration); spread is the largest (max - min) / min over the rounds of one configuration.
import json, pathlib, sys

N = 1024
here = pathlib.Path(sys.argv[1])
dropped = set(sys.argv[2:])
CONFIGS = ["aarch64-b5dd856", "aarch64-7e92e46", "generic-b5dd856", "generic-7e92e46"]
INTERVALS = (
    [f"add/{c}" for c in ["PP", "PM", "MM"]]
    + [f"sub/{c}" for c in ["PP", "PM", "MM"]]
    + [f"mul/{c}" for c in ["PP", "PN", "PM", "NP", "NN", "NM", "MP", "MN", "MM"]]
    + [f"mul_tiny/{c}" for c in ["PP", "PN", "PM", "NP", "NN", "NM", "MP", "MN", "MM"]]
    + [f"div/{c}" for c in ["PP", "PN", "MP", "NN", "PM"]]
    + ["unary/sqrt_P", "unary/sqrt_M", "unary/horner8_P", "unary/horner8_M", "unary/det3_mixed"]
)
LABELS = {
    "div/PM": "div/PM (= ℝ)", "unary/sqrt_P": "sqrt/P", "unary/sqrt_M": "sqrt/M",
    "unary/horner8_P": "Horner, degree 8, P", "unary/horner8_M": "Horner, degree 8, M",
    "unary/det3_mixed": "3×3 determinant",
    "unary/horner8_mul_add_P": "Horner `mul_add`, degree 8, P",
    "unary/horner8_mul_add_M": "Horner `mul_add`, degree 8, M",
}
PRIMITIVES = [f"{p}/{k}/1024" for p in ["add_ru", "mul_ru", "div_ru", "mul_add_ru", "sqrt1_ru"]
              for k in ["throughput", "latency"]]

def medians(config, bench):
    build, commit = config.split("-")
    out = []
    for d in sorted((here / bench).glob(f"{commit}-{build}-r*")):
        if d.name in dropped:
            continue
        out.append(json.loads((d / "estimates.json").read_text())["median"]["point_estimate"] / N)
    return out

above = []
def table(benches):
    print("| Benchmark | aarch64 b5dd856 (ns) | aarch64 7e92e46 (ns) | aarch64 7e92e46 / b5dd856 "
          "| generic b5dd856 (ns) | generic 7e92e46 (ns) | generic 7e92e46 / b5dd856 | spread |")
    print("|---|--:|--:|--:|--:|--:|--:|--:|")
    for b in benches:
        m = {c: medians(c, b) for c in CONFIGS}
        assert all(m.values()), b
        lo = {c: min(v) for c, v in m.items()}
        sp = max((max(v) - min(v)) / min(v) for v in m.values())
        ra = lo["aarch64-7e92e46"] / lo["aarch64-b5dd856"]
        rg = lo["generic-7e92e46"] / lo["generic-b5dd856"]
        label = LABELS.get(b, b.removesuffix("/1024"))
        for name, r in [("aarch64", ra), ("generic", rg)]:
            if r - 1 > sp:
                above.append(f"{label}, {name}: {r:.3f}× (spread {sp:.1%})")
        print(f"| {label} | {lo['aarch64-b5dd856']:.2f} | {lo['aarch64-7e92e46']:.2f} | {ra:.3f}× "
              f"| {lo['generic-b5dd856']:.2f} | {lo['generic-7e92e46']:.2f} | {rg:.3f}× | {sp:.1%} |")

rounds = sorted({f.parent.name for f in here.rglob("*-r*/estimates.json")
                 if not f.parent.name.startswith("asin-")} - dropped)
print("Rounds:", ", ".join(rounds)); print()
table(INTERVALS); print()
print("| Benchmark (7e92e46 only) | aarch64 (ns) | generic (ns) | spread |")
print("|---|--:|--:|--:|")
for b in ["unary/horner8_mul_add_P", "unary/horner8_mul_add_M"]:
    m = {c: medians(c, b) for c in ["aarch64-7e92e46", "generic-7e92e46"]}
    sp = max((max(v) - min(v)) / min(v) for v in m.values())
    print(f"| {LABELS[b]} | {min(m['aarch64-7e92e46']):.2f} | {min(m['generic-7e92e46']):.2f} | {sp:.1%} |")
print(); table(PRIMITIVES); print()
print("Above 1 by more than the spread:"); print("\n".join(above) or "none")

# The token API's series: criterion keeps `token/<group>` as `token_<group>`.
tok = sorted(p.parent for p in here.glob("token_*/**/7e92e46-token-r1/estimates.json"))
if tok:
    print(); print("| Series | operators (ns) | token (ns) | token / operators |"); print("|---|--:|--:|--:|")
    for d in tok:
        rel = d.parent.relative_to(here).as_posix().removeprefix("token_")
        t = json.loads((d / "estimates.json").read_text())["median"]["point_estimate"] / N
        o = min(medians("aarch64-7e92e46", rel))
        print(f"| token/{LABELS.get(rel, rel)} | {o:.2f} | {t:.2f} | {t/o:.3f}× |")

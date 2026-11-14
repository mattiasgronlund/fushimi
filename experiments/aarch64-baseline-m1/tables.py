"""Prints the tables of issue #3 from criterion/<config>-r<n>/.../estimates.json.

Each cell is the lowest of the rounds' medians per operation (every benchmark
times N = 1024 operations per iteration), and `spread` is the largest
difference between the rounds of one configuration in that row, relative to
the lower one, as in BENCHMARKS.md's "Variance". Run from this directory.
"""

import json
import pathlib

N = 1024
CONFIGS = ["aarch64", "generic"]
here = pathlib.Path(__file__).parent / "criterion"

INTERVALS = (
    [f"add/{c}" for c in ["PP", "PM", "MM"]]
    + [f"sub/{c}" for c in ["PP", "PM", "MM"]]
    + [f"mul/{c}" for c in ["PP", "PN", "PM", "NP", "NN", "NM", "MP", "MN", "MM"]]
    + [f"mul_tiny/{c}" for c in ["PP", "PN", "PM", "NP", "NN", "NM", "MP", "MN", "MM"]]
    + [f"div/{c}" for c in ["PP", "PN", "MP", "NN", "PM"]]
    + ["unary/sqrt_P", "unary/sqrt_M", "unary/horner8_P", "unary/horner8_M", "unary/det3_mixed"]
)
LABELS = {
    "div/PM": "div/PM (= ℝ)",
    "unary/sqrt_P": "sqrt/P",
    "unary/sqrt_M": "sqrt/M",
    "unary/horner8_P": "Horner, degree 8, P",
    "unary/horner8_M": "Horner, degree 8, M",
    "unary/det3_mixed": "3×3 determinant",
}
PRIMITIVES = [
    f"{p}/{k}/1024"
    for p in ["add_ru", "mul_ru", "div_ru", "mul_add_ru", "sqrt1_ru"]
    for k in ["throughput", "latency"]
]


def medians(config, bench):
    out = []
    for d in sorted(here.glob(f"{config}-r*")):
        f = d / bench / "estimates.json"
        if f.exists():
            out.append(json.loads(f.read_text())["median"]["point_estimate"] / N)
    return out


def table(benches):
    print("| Benchmark | aarch64 (ns) | generic (ns) | generic / aarch64 | spread |")
    print("|---|--:|--:|--:|--:|")
    for b in benches:
        m = {c: medians(c, b) for c in CONFIGS}
        lo = {c: min(m[c]) for c in CONFIGS}
        spread = max((max(m[c]) - lo[c]) / lo[c] for c in CONFIGS)
        label = LABELS.get(b, b.removesuffix("/1024"))
        print(
            f"| {label} | {lo['aarch64']:.2f} | {lo['generic']:.2f} "
            f"| {lo['generic'] / lo['aarch64']:.2f}× | {spread:.0%} |"
        )


print("Rounds:", ", ".join(d.name for d in sorted(here.iterdir())))
print()
table(INTERVALS)
print()
table(PRIMITIVES)

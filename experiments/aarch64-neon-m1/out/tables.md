Rounds kept: V1-r1, V1-r2, V1-r3, V1-r4, V1-r5, V24-r1, V24-r2, V24-r3, V24-r4, V24-r5, V246s-r1, V246s-r2, V246s-r3, V246s-r4, V246s-r5, V6s-r1, V6s-r2, V6s-r3, V6s-r4, V6s-r5, fpcr-r1, fpcr-r2, fpcr-r3, fpcr-r4, fpcr-r5, generic-r1, generic-r2, generic-r3, generic-r4, generic-r5, neon-r1, neon-r2, neon-r3, neon-r4, neon-r5

## Interval operations (`intervals`)

| Benchmark | fpcr (ns) | generic (ns) | neon (ns) | neon / fpcr | neon / generic | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 23.29 | 4.22 | 2.02 | 0.09× | 0.48× | 3% |
| add/PM | 23.29 | 5.14 | 2.02 | 0.09× | 0.39× | 2% |
| add/MM | 23.29 | 4.29 | 2.02 | 0.09× | 0.47× | 5% |
| sub/PP | 23.59 | 4.08 | 2.18 | 0.09× | 0.53× | 0% |
| sub/PM | 23.60 | 5.44 | 2.18 | 0.09× | 0.40× | 4% |
| sub/MM | 23.60 | 4.35 | 2.18 | 0.09× | 0.50× | 3% |
| mul/PP | 29.29 | 14.80 | 4.35 | 0.15× | 0.29× | 0% |
| mul/PN | 29.29 | 14.62 | 4.35 | 0.15× | 0.30× | 1% |
| mul/PM | 29.29 | 14.66 | 4.35 | 0.15× | 0.30× | 0% |
| mul/NP | 29.28 | 14.64 | 4.35 | 0.15× | 0.30× | 1% |
| mul/NN | 29.48 | 14.90 | 4.35 | 0.15× | 0.29× | 0% |
| mul/NM | 29.29 | 14.82 | 4.35 | 0.15× | 0.29× | 0% |
| mul/MP | 29.29 | 14.08 | 4.04 | 0.14× | 0.29× | 0% |
| mul/MN | 29.28 | 14.33 | 4.35 | 0.15× | 0.30× | 1% |
| mul/MM | 49.86 | 27.63 | 6.19 | 0.12× | 0.22× | 1% |
| mul_tiny/PP | 29.29 | 18.88 | 6.52 | 0.22× | 0.35× | 1% |
| mul_tiny/PN | 29.29 | 18.25 | 6.52 | 0.22× | 0.36× | 2% |
| mul_tiny/PM | 29.29 | 19.50 | 6.52 | 0.22× | 0.33× | 1% |
| mul_tiny/NP | 29.29 | 18.34 | 6.52 | 0.22× | 0.36× | 1% |
| mul_tiny/NN | 29.48 | 18.97 | 6.52 | 0.22× | 0.34× | 1% |
| mul_tiny/NM | 29.29 | 19.65 | 6.52 | 0.22× | 0.33× | 0% |
| mul_tiny/MP | 29.29 | 19.24 | 6.31 | 0.22× | 0.33× | 1% |
| mul_tiny/MN | 29.29 | 19.51 | 6.52 | 0.22× | 0.33× | 1% |
| mul_tiny/MM | 49.86 | 37.17 | 10.58 | 0.21× | 0.28× | 1% |
| div/PP | 31.23 | 8.15 | 4.27 | 0.14× | 0.52× | 13% |
| div/PN | 31.22 | 8.25 | 4.35 | 0.14× | 0.53× | 5% |
| div/MP | 31.22 | 8.37 | 4.23 | 0.14× | 0.51× | 19% |
| div/NN | 31.23 | 8.48 | 4.27 | 0.14× | 0.50× | 31% |
| div/PM | 2.33 | 2.84 | 2.60 | 1.12× | 0.92× | 0% |
| mul_add/PPP | 29.80 | 12.28 | 7.69 | 0.26× | 0.63× | 7% |
| mul_add/PNM | 29.92 | 12.64 | 7.78 | 0.26× | 0.62× | 4% |
| mul_add/MMM | 49.88 | 26.32 | 11.99 | 0.24× | 0.46× | 11% |
| mul_add_tiny/PPP | 29.80 | 26.81 | 30.30 | 1.02× | 1.13× | 0% |
| mul_add_tiny/PNM | 29.93 | 26.96 | 29.95 | 1.00× | 1.11× | 0% |
| mul_add_tiny/MMM | 49.88 | 51.24 | 56.65 | 1.14× | 1.11× | 0% |
| unary/sqrt/P | 50.21 | 4.25 | 3.05 | 0.06× | 0.72× | 15% |
| unary/sqrt/M | 27.43 | 3.68 | 3.52 | 0.13× | 0.95× | 6% |
| unary/horner8/P | 380.75 | 157.07 | 84.95 | 0.22× | 0.54× | 1% |
| unary/horner8/M | 525.75 | 267.22 | 108.76 | 0.21× | 0.41× | 0% |
| unary/horner8_mul_add/P | 235.34 | 168.72 | 114.66 | 0.49× | 0.68× | 7% |
| unary/horner8_mul_add/M | 381.25 | 332.61 | 135.14 | 0.35× | 0.41× | 2% |
| unary/det3/mixed | 363.74 | 157.99 | 41.85 | 0.12× | 0.26× | 8% |
| token/add/PP | 23.92 | 3.70 | 1.45 | 0.06× | 0.39× | 4% |
| token/add/PM | 23.92 | 4.01 | 1.45 | 0.06× | 0.36× | 1% |
| token/add/MM | 23.93 | 3.72 | 1.45 | 0.06× | 0.39× | 2% |
| token/mul/PP | 30.13 | 14.18 | 3.11 | 0.10× | 0.22× | 1% |
| token/mul/PN | 29.98 | 13.97 | 3.11 | 0.10× | 0.22× | 0% |
| token/mul/PM | 30.15 | 13.84 | 3.11 | 0.10× | 0.22× | 1% |
| token/mul/NP | 30.15 | 13.88 | 3.11 | 0.10× | 0.22× | 0% |
| token/mul/NN | 29.98 | 14.36 | 3.11 | 0.10× | 0.22× | 0% |
| token/mul/NM | 30.15 | 14.20 | 3.11 | 0.10× | 0.22× | 0% |
| token/mul/MP | 29.98 | 13.53 | 2.91 | 0.10× | 0.22× | 0% |
| token/mul/MN | 30.14 | 13.68 | 3.11 | 0.10× | 0.23× | 0% |
| token/mul/MM | 50.07 | 22.80 | 4.90 | 0.10× | 0.21× | 2% |
| token/mul_tiny/PP | 30.13 | 18.12 | 5.29 | 0.18× | 0.29× | 2% |
| token/mul_tiny/PN | 29.97 | 17.14 | 5.35 | 0.18× | 0.31× | 1% |
| token/mul_tiny/PM | 30.16 | 16.20 | 5.28 | 0.18× | 0.33× | 0% |
| token/mul_tiny/NP | 30.16 | 17.10 | 5.36 | 0.18× | 0.31× | 1% |
| token/mul_tiny/NN | 29.98 | 17.92 | 5.30 | 0.18× | 0.30× | 1% |
| token/mul_tiny/NM | 30.15 | 18.71 | 5.28 | 0.18× | 0.28× | 1% |
| token/mul_tiny/MP | 29.98 | 18.66 | 5.28 | 0.18× | 0.28× | 1% |
| token/mul_tiny/MN | 30.15 | 18.51 | 5.28 | 0.18× | 0.29× | 1% |
| token/mul_tiny/MM | 50.08 | 38.12 | 9.51 | 0.19× | 0.25× | 2% |
| token/div/PP | 31.88 | 7.51 | 3.26 | 0.10× | 0.43× | 12% |
| token/div/PN | 32.06 | 7.11 | 3.29 | 0.10× | 0.46× | 8% |
| token/div/MP | 32.05 | 7.90 | 3.16 | 0.10× | 0.40× | 25% |
| token/div/NN | 31.93 | 8.19 | 3.31 | 0.10× | 0.40× | 11% |
| token/div/PM | 1.71 | 1.90 | 1.67 | 0.98× | 0.88× | 0% |
| token/unary/sqrt/P | 50.17 | 3.43 | 2.33 | 0.05× | 0.68× | 3% |
| token/unary/sqrt/M | 27.10 | 2.20 | 1.85 | 0.07× | 0.84× | 13% |
| token/unary/horner8/P | 375.65 | 162.68 | 73.64 | 0.20× | 0.45× | 0% |
| token/unary/horner8/M | 511.37 | 249.60 | 94.57 | 0.18× | 0.38× | 0% |
| token/unary/horner8_mul_add/P | 215.64 | 122.78 | 84.71 | 0.39× | 0.69× | 5% |
| token/unary/horner8_mul_add/M | 351.70 | 286.77 | 104.75 | 0.30× | 0.37× | 3% |
| token/unary/det3/mixed | 348.34 | 145.59 | 34.71 | 0.10× | 0.24× | 3% |

## Primitives (`primitives`)

| Benchmark | fpcr (ns) | generic (ns) | neon (ns) | neon / fpcr | neon / generic | spread |
|---|--:|--:|--:|--:|--:|--:|
| add_ru/throughput/1024 | 23.36 | 4.08 | 1.90 | 0.08× | 0.47× | 0% |
| add_ru/latency/1024 | 22.04 | 9.31 | 6.54 | 0.30× | 0.70× | 0% |
| mul_ru/throughput/1024 | 23.65 | 13.51 | 2.25 | 0.10× | 0.17× | 1% |
| mul_ru/latency/1024 | 22.35 | 16.00 | 4.52 | 0.20× | 0.28× | 1% |
| div_ru/throughput/1024 | 25.52 | 5.85 | 2.64 | 0.10× | 0.45× | 7% |
| div_ru/latency/1024 | 24.21 | 11.65 | 7.01 | 0.29× | 0.60× | 2% |
| mul_add_ru/throughput/1024 | 23.61 | 7.63 | 4.82 | 0.20× | 0.63× | 7% |
| mul_add_ru/latency/1024 | 21.73 | 6.35 | 11.83 | 0.54× | 1.86× | 0% |
| mul_add_ru/latency_inexact/1024 | 21.42 | 24.16 | 11.89 | 0.56× | 0.49× | 0% |
| sqrt1_ru/throughput/1024 | 25.20 | 1.57 | 1.57 | 0.06× | 1.00× | 9% |
| sqrt1_ru/latency/1024 | 24.53 | 8.55 | 8.55 | 0.35× | 1.00× | 0% |

## Variants of `mul_add_ru`

| Benchmark | neon (ns) | V1 (ns) | V24 (ns) | V6s (ns) | V246s (ns) | V1 / neon | V24 / neon | V6s / neon | V246s / neon | generic (ns) | spread |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| mul_add/PPP | 7.69 | 7.70 | 7.77 | 7.77 | 7.88 | 1.00× | 1.01× | 1.01× | 1.02× | 12.28 | 7% |
| mul_add/PNM | 7.78 | 8.12 | 7.92 | 7.92 | 7.96 | 1.04× | 1.02× | 1.02× | 1.02× | 12.64 | 5% |
| mul_add/MMM | 11.99 | 12.27 | 12.07 | 12.10 | 12.27 | 1.02× | 1.01× | 1.01× | 1.02× | 26.32 | 11% |
| mul_add_tiny/PPP | 30.30 | 30.81 | 30.30 | 30.30 | 30.30 | 1.02× | 1.00× | 1.00× | 1.00× | 26.81 | 0% |
| mul_add_tiny/PNM | 29.95 | 31.11 | 29.95 | 29.95 | 29.95 | 1.04× | 1.00× | 1.00× | 1.00× | 26.96 | 0% |
| mul_add_tiny/MMM | 56.65 | 58.88 | 56.69 | 56.65 | 56.65 | 1.04× | 1.00× | 1.00× | 1.00× | 51.24 | 0% |
| unary/horner8_mul_add/P | 114.66 | 104.63 | 109.78 | 111.08 | 106.33 | 0.91× | 0.96× | 0.97× | 0.93× | 168.72 | 8% |
| unary/horner8_mul_add/M | 135.14 | 149.33 | 131.19 | 132.35 | 128.35 | 1.10× | 0.97× | 0.98× | 0.95× | 332.61 | 9% |
| token/unary/horner8_mul_add/P | 84.71 | 64.81 | 80.30 | 82.56 | 79.41 | 0.77× | 0.95× | 0.97× | 0.94× | 122.78 | 16% |
| token/unary/horner8_mul_add/M | 104.75 | 119.30 | 101.54 | 102.51 | 99.20 | 1.14× | 0.97× | 0.98× | 0.95× | 286.77 | 8% |
| mul_add_ru/throughput/1024 | 4.82 | 5.13 | 4.89 | 4.89 | 5.12 | 1.06× | 1.02× | 1.02× | 1.06× | 7.63 | 7% |
| mul_add_ru/latency/1024 | 11.83 | 4.63 | 10.82 | 11.22 | 10.16 | 0.39× | 0.91× | 0.95× | 0.86× | 6.35 | 0% |
| mul_add_ru/latency_inexact/1024 | 11.89 | 13.82 | 10.95 | 11.30 | 10.30 | 1.16× | 0.92× | 0.95× | 0.87× | 24.16 | 0% |

## Against issue #4

Benchmarks in both issues: 44; cells that don't agree: 75

| Benchmark | Columns | this (ns) | #4 (ns) | ratio | larger spread |
|---|---|--:|--:|--:|--:|
| mul/PP | fpcr / #4 aarch64 | 29.29 | 32.09 | 0.91× | 0% |
| mul/PP | generic / #4 generic | 14.80 | 14.91 | 0.99× | 0% |
| mul/PP | neon / #4 proto | 4.35 | 3.89 | 1.12× | 1% |
| mul/PN | fpcr / #4 aarch64 | 29.29 | 31.97 | 0.92× | 0% |
| mul/PN | generic / #4 generic | 14.62 | 14.74 | 0.99× | 1% |
| mul/PN | neon / #4 proto | 4.35 | 3.89 | 1.12× | 1% |
| mul/PM | fpcr / #4 aarch64 | 29.29 | 31.96 | 0.92× | 1% |
| mul/PM | generic / #4 generic | 14.66 | 14.75 | 0.99× | 0% |
| mul/PM | neon / #4 proto | 4.35 | 3.85 | 1.13× | 2% |
| mul/NP | fpcr / #4 aarch64 | 29.28 | 31.98 | 0.92× | 0% |
| mul/NP | generic / #4 generic | 14.64 | 14.79 | 0.99× | 1% |
| mul/NP | neon / #4 proto | 4.35 | 3.89 | 1.12× | 1% |
| mul/NN | fpcr / #4 aarch64 | 29.48 | 31.97 | 0.92× | 0% |
| mul/NN | generic / #4 generic | 14.90 | 14.99 | 0.99× | 0% |
| mul/NN | neon / #4 proto | 4.35 | 3.97 | 1.10× | 1% |
| mul/NM | fpcr / #4 aarch64 | 29.29 | 31.97 | 0.92× | 0% |
| mul/NM | generic / #4 generic | 14.82 | 14.92 | 0.99× | 0% |
| mul/NM | neon / #4 proto | 4.35 | 3.92 | 1.11× | 1% |
| mul/MP | fpcr / #4 aarch64 | 29.29 | 31.96 | 0.92× | 0% |
| mul/MP | generic / #4 generic | 14.08 | 14.26 | 0.99× | 0% |
| mul/MP | neon / #4 proto | 4.04 | 3.81 | 1.06× | 1% |
| mul/MN | fpcr / #4 aarch64 | 29.28 | 31.97 | 0.92× | 0% |
| mul/MN | generic / #4 generic | 14.33 | 14.45 | 0.99× | 1% |
| mul/MN | neon / #4 proto | 4.35 | 3.89 | 1.12× | 2% |
| mul/MM | fpcr / #4 aarch64 | 49.86 | 52.18 | 0.96× | 0% |
| mul/MM | generic / #4 generic | 27.63 | 27.91 | 0.99× | 1% |
| mul/MM | neon / #4 proto | 6.19 | 5.72 | 1.08× | 0% |
| mul_tiny/PP | fpcr / #4 aarch64 | 29.29 | 31.97 | 0.92× | 0% |
| mul_tiny/PP | generic / #4 generic | 18.88 | 18.10 | 1.04× | 1% |
| mul_tiny/PP | neon / #4 proto | 6.52 | 6.22 | 1.05× | 1% |
| mul_tiny/PN | fpcr / #4 aarch64 | 29.29 | 31.97 | 0.92× | 1% |
| mul_tiny/PN | generic / #4 generic | 18.25 | 17.66 | 1.03× | 2% |
| mul_tiny/PN | neon / #4 proto | 6.52 | 6.23 | 1.05× | 0% |
| mul_tiny/PM | fpcr / #4 aarch64 | 29.29 | 31.96 | 0.92× | 0% |
| mul_tiny/PM | generic / #4 generic | 19.50 | 18.23 | 1.07× | 1% |
| mul_tiny/PM | neon / #4 proto | 6.52 | 6.21 | 1.05× | 0% |
| mul_tiny/NP | fpcr / #4 aarch64 | 29.29 | 31.97 | 0.92× | 1% |
| mul_tiny/NP | generic / #4 generic | 18.34 | 17.50 | 1.05× | 3% |
| mul_tiny/NP | neon / #4 proto | 6.52 | 6.23 | 1.05× | 1% |
| mul_tiny/NN | fpcr / #4 aarch64 | 29.48 | 31.97 | 0.92× | 0% |
| mul_tiny/NN | generic / #4 generic | 18.97 | 17.84 | 1.06× | 1% |
| mul_tiny/NN | neon / #4 proto | 6.52 | 6.27 | 1.04× | 0% |
| mul_tiny/NM | fpcr / #4 aarch64 | 29.29 | 31.97 | 0.92× | 0% |
| mul_tiny/NM | generic / #4 generic | 19.65 | 18.38 | 1.07× | 0% |
| mul_tiny/NM | neon / #4 proto | 6.52 | 6.25 | 1.04× | 0% |
| mul_tiny/MP | fpcr / #4 aarch64 | 29.29 | 31.97 | 0.92× | 0% |
| mul_tiny/MP | generic / #4 generic | 19.24 | 17.51 | 1.10× | 3% |
| mul_tiny/MP | neon / #4 proto | 6.31 | 6.11 | 1.03× | 1% |
| mul_tiny/MN | fpcr / #4 aarch64 | 29.29 | 31.96 | 0.92× | 0% |
| mul_tiny/MN | generic / #4 generic | 19.51 | 17.65 | 1.11× | 2% |
| mul_tiny/MN | neon / #4 proto | 6.52 | 6.22 | 1.05× | 0% |
| mul_tiny/MM | fpcr / #4 aarch64 | 49.86 | 52.17 | 0.96× | 0% |
| mul_tiny/MM | generic / #4 generic | 37.17 | 35.36 | 1.05× | 1% |
| mul_tiny/MM | neon / #4 proto | 10.58 | 10.26 | 1.03× | 1% |
| div/PP | fpcr / #4 aarch64 | 31.23 | 33.63 | 0.93× | 0% |
| div/PP | neon / #4 proto | 4.27 | 4.24 | 1.01× | 1% |
| div/PN | fpcr / #4 aarch64 | 31.22 | 33.63 | 0.93× | 0% |
| div/PN | generic / #4 generic | 8.25 | 7.56 | 1.09× | 5% |
| div/PN | neon / #4 proto | 4.35 | 4.27 | 1.02× | 1% |
| div/MP | fpcr / #4 aarch64 | 31.22 | 33.63 | 0.93× | 1% |
| div/NN | fpcr / #4 aarch64 | 31.23 | 33.63 | 0.93× | 1% |
| div/PM | fpcr / #4 aarch64 | 2.33 | 2.64 | 0.88× | 1% |
| unary/horner8/P | fpcr / #4 aarch64 | 380.75 | 400.22 | 0.95× | 0% |
| unary/horner8/P | generic / #4 generic | 157.07 | 158.31 | 0.99× | 1% |
| unary/horner8/P | neon / #4 proto | 84.95 | 85.49 | 0.99× | 1% |
| unary/horner8/M | fpcr / #4 aarch64 | 525.75 | 547.36 | 0.96× | 1% |
| unary/horner8/M | neon / #4 proto | 108.76 | 98.19 | 1.11× | 0% |
| unary/det3/mixed | fpcr / #4 aarch64 | 363.74 | 384.94 | 0.94× | 1% |
| unary/det3/mixed | neon / #4 proto | 41.85 | 39.18 | 1.07× | 0% |
| add_ru/throughput/1024 | generic / #4 generic | 4.08 | 4.04 | 1.01× | 0% |
| mul_ru/throughput/1024 | generic / #4 generic | 13.51 | 11.96 | 1.13× | 1% |
| mul_ru/latency/1024 | generic / #4 generic | 16.00 | 15.01 | 1.07× | 1% |
| div_ru/latency/1024 | generic / #4 generic | 11.65 | 11.12 | 1.05× | 2% |
| mul_add_ru/throughput/1024 | neon / #4 proto | 4.82 | 4.89 | 0.98× | 0% |
| mul_add_ru/latency/1024 | neon / #4 proto | 11.83 | 12.72 | 0.93× | 0% |

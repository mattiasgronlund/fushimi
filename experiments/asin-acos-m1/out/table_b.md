Rounds: 7e92e46-aarch64-r1, 7e92e46-aarch64-r4, 7e92e46-generic-r1, 7e92e46-generic-r2, 7e92e46-generic-r3, 7e92e46-token-r1, b5dd856-aarch64-r1, b5dd856-aarch64-r2, b5dd856-aarch64-r3, b5dd856-aarch64-r4, b5dd856-generic-r1, b5dd856-generic-r3, b5dd856-generic-r4

| Benchmark | aarch64 b5dd856 (ns) | aarch64 7e92e46 (ns) | aarch64 7e92e46 / b5dd856 | generic b5dd856 (ns) | generic 7e92e46 (ns) | generic 7e92e46 / b5dd856 | spread |
|---|--:|--:|--:|--:|--:|--:|--:|
| add/PP | 23.27 | 23.30 | 1.001× | 4.22 | 4.26 | 1.010× | 1.7% |
| add/PM | 23.27 | 23.30 | 1.001× | 5.19 | 5.19 | 1.001× | 2.0% |
| add/MM | 23.27 | 23.30 | 1.001× | 4.46 | 4.27 | 0.957× | 3.5% |
| sub/PP | 23.57 | 23.59 | 1.001× | 4.08 | 4.08 | 1.000× | 0.7% |
| sub/PM | 23.57 | 23.59 | 1.001× | 5.51 | 5.46 | 0.990× | 0.7% |
| sub/MM | 23.57 | 23.59 | 1.001× | 4.43 | 4.26 | 0.961× | 4.2% |
| mul/PP | 29.27 | 29.28 | 1.000× | 14.93 | 14.81 | 0.993× | 0.5% |
| mul/PN | 29.27 | 29.28 | 1.000× | 14.75 | 14.60 | 0.990× | 0.5% |
| mul/PM | 29.26 | 29.28 | 1.000× | 14.75 | 14.64 | 0.992× | 0.8% |
| mul/NP | 29.27 | 29.28 | 1.000× | 14.76 | 14.72 | 0.997× | 0.7% |
| mul/NN | 29.46 | 29.47 | 1.000× | 14.95 | 14.90 | 0.997× | 0.8% |
| mul/NM | 29.27 | 29.28 | 1.000× | 14.90 | 14.86 | 0.997× | 1.4% |
| mul/MP | 29.27 | 29.28 | 1.000× | 14.27 | 14.09 | 0.988× | 1.3% |
| mul/MN | 29.27 | 29.28 | 1.000× | 14.46 | 14.44 | 0.999× | 1.1% |
| mul/MM | 49.83 | 49.84 | 1.000× | 27.91 | 27.64 | 0.990× | 1.4% |
| mul_tiny/PP | 29.27 | 29.28 | 1.000× | 18.06 | 18.77 | 1.039× | 2.0% |
| mul_tiny/PN | 29.27 | 29.28 | 1.000× | 17.88 | 18.41 | 1.030× | 1.1% |
| mul_tiny/PM | 29.27 | 29.28 | 1.000× | 18.23 | 19.59 | 1.074× | 1.3% |
| mul_tiny/NP | 29.27 | 29.28 | 1.000× | 17.63 | 18.26 | 1.036× | 2.5% |
| mul_tiny/NN | 29.46 | 29.47 | 1.000× | 18.02 | 18.82 | 1.045× | 1.2% |
| mul_tiny/NM | 29.27 | 29.28 | 1.000× | 18.37 | 19.67 | 1.071× | 1.7% |
| mul_tiny/MP | 29.27 | 29.28 | 1.000× | 17.69 | 19.22 | 1.086× | 1.0% |
| mul_tiny/MN | 29.26 | 29.28 | 1.000× | 17.64 | 19.60 | 1.111× | 2.0% |
| mul_tiny/MM | 49.83 | 49.84 | 1.000× | 35.48 | 37.32 | 1.052× | 2.2% |
| div/PP | 31.20 | 31.21 | 1.000× | 7.05 | 7.33 | 1.040× | 12.2% |
| div/PN | 31.20 | 31.21 | 1.000× | 7.18 | 7.36 | 1.026× | 3.6% |
| div/MP | 31.20 | 31.21 | 1.000× | 7.03 | 7.12 | 1.013× | 6.3% |
| div/NN | 31.20 | 31.21 | 1.000× | 6.96 | 7.47 | 1.074× | 5.1% |
| div/PM (= ℝ) | 2.33 | 2.33 | 1.000× | 2.84 | 2.83 | 0.999× | 1.2% |
| sqrt/P | 50.19 | 50.20 | 1.000× | 4.23 | 4.18 | 0.989× | 6.3% |
| sqrt/M | 27.41 | 27.42 | 1.000× | 3.75 | 3.97 | 1.058× | 2.8% |
| Horner, degree 8, P | 380.39 | 380.98 | 1.002× | 158.07 | 157.86 | 0.999× | 0.8% |
| Horner, degree 8, M | 525.67 | 525.91 | 1.000× | 267.45 | 266.89 | 0.998× | 0.7% |
| 3×3 determinant | 363.41 | 363.57 | 1.000× | 149.48 | 168.48 | 1.127× | 7.3% |

| Benchmark (7e92e46 only) | aarch64 (ns) | generic (ns) | spread |
|---|--:|--:|--:|
| Horner `mul_add`, degree 8, P | 223.96 | 161.78 | 2.8% |
| Horner `mul_add`, degree 8, M | 368.57 | 322.08 | 4.1% |

| Benchmark | aarch64 b5dd856 (ns) | aarch64 7e92e46 (ns) | aarch64 7e92e46 / b5dd856 | generic b5dd856 (ns) | generic 7e92e46 (ns) | generic 7e92e46 / b5dd856 | spread |
|---|--:|--:|--:|--:|--:|--:|--:|
| add_ru/throughput | 23.36 | 23.37 | 1.001× | 4.04 | 4.08 | 1.009× | 1.1% |
| add_ru/latency | 22.02 | 22.03 | 1.000× | 9.33 | 9.31 | 0.998× | 0.6% |
| mul_ru/throughput | 23.65 | 23.64 | 1.000× | 11.81 | 13.56 | 1.148× | 3.8% |
| mul_ru/latency | 22.33 | 22.34 | 1.000× | 14.99 | 15.99 | 1.066× | 1.7% |
| div_ru/throughput | 25.49 | 25.51 | 1.001× | 5.81 | 5.85 | 1.006× | 9.3% |
| div_ru/latency | 24.19 | 24.20 | 1.000× | 11.12 | 11.51 | 1.034× | 1.4% |
| mul_add_ru/throughput | 23.60 | 23.60 | 1.000× | 7.80 | 7.61 | 0.975× | 4.6% |
| mul_add_ru/latency | 21.72 | 21.72 | 1.000× | 6.35 | 6.34 | 0.999× | 0.7% |
| sqrt1_ru/throughput | 25.20 | 25.20 | 1.000× | 1.57 | 1.57 | 0.999× | 2.7% |
| sqrt1_ru/latency | 24.52 | 24.53 | 1.000× | 8.55 | 8.54 | 0.999× | 0.7% |

Above 1 by more than the spread:
mul_tiny/PP, generic: 1.039× (spread 2.0%)
mul_tiny/PN, generic: 1.030× (spread 1.1%)
mul_tiny/PM, generic: 1.074× (spread 1.3%)
mul_tiny/NP, generic: 1.036× (spread 2.5%)
mul_tiny/NN, generic: 1.045× (spread 1.2%)
mul_tiny/NM, generic: 1.071× (spread 1.7%)
mul_tiny/MP, generic: 1.086× (spread 1.0%)
mul_tiny/MN, generic: 1.111× (spread 2.0%)
mul_tiny/MM, generic: 1.052× (spread 2.2%)
div/NN, generic: 1.074× (spread 5.1%)
sqrt/M, generic: 1.058× (spread 2.8%)
3×3 determinant, generic: 1.127× (spread 7.3%)
mul_ru/throughput, generic: 1.148× (spread 3.8%)
mul_ru/latency, generic: 1.066× (spread 1.7%)
div_ru/latency, generic: 1.034× (spread 1.4%)

| Series | operators (ns) | token (ns) | token / operators |
|---|--:|--:|--:|
| token/add/MM | 23.30 | 23.94 | 1.027× |
| token/add/PM | 23.30 | 23.96 | 1.028× |
| token/add/PP | 23.30 | 24.01 | 1.031× |
| token/div/MP | 31.21 | 32.14 | 1.030× |
| token/div/NN | 31.21 | 31.95 | 1.024× |
| token/div/PM (= ℝ) | 2.33 | 1.71 | 0.735× |
| token/div/PN | 31.21 | 32.13 | 1.029× |
| token/div/PP | 31.21 | 31.91 | 1.022× |
| token/mul/MM | 49.84 | 50.32 | 1.010× |
| token/mul/MN | 29.28 | 30.26 | 1.034× |
| token/mul/MP | 29.28 | 30.28 | 1.034× |
| token/mul/NM | 29.28 | 30.21 | 1.032× |
| token/mul/NN | 29.47 | 30.01 | 1.018× |
| token/mul/NP | 29.28 | 30.23 | 1.033× |
| token/mul/PM | 29.28 | 30.22 | 1.032× |
| token/mul/PN | 29.28 | 30.05 | 1.026× |
| token/mul/PP | 29.28 | 30.15 | 1.030× |
| token/mul_tiny/MM | 49.84 | 50.20 | 1.007× |
| token/mul_tiny/MN | 29.28 | 30.22 | 1.032× |
| token/mul_tiny/MP | 29.28 | 30.07 | 1.027× |
| token/mul_tiny/NM | 29.28 | 30.33 | 1.036× |
| token/mul_tiny/NN | 29.47 | 30.08 | 1.021× |
| token/mul_tiny/NP | 29.28 | 30.25 | 1.033× |
| token/mul_tiny/PM | 29.28 | 30.31 | 1.035× |
| token/mul_tiny/PN | 29.28 | 30.10 | 1.028× |
| token/mul_tiny/PP | 29.28 | 30.31 | 1.035× |
| token/3×3 determinant | 363.57 | 349.05 | 0.960× |
| token/Horner, degree 8, M | 525.91 | 511.67 | 0.973× |
| token/Horner, degree 8, P | 380.98 | 376.00 | 0.987× |
| token/Horner `mul_add`, degree 8, M | 368.57 | 351.88 | 0.955× |
| token/Horner `mul_add`, degree 8, P | 223.96 | 215.84 | 0.964× |
| token/sqrt/M | 27.42 | 27.11 | 0.989× |
| token/sqrt/P | 50.20 | 50.18 | 1.000× |

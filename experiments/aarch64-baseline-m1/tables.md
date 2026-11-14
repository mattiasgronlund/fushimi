Rounds: aarch64-r1, aarch64-r2, aarch64-r4, generic-r2, generic-r3, generic-r4

| Benchmark | aarch64 (ns) | generic (ns) | generic / aarch64 | spread |
|---|--:|--:|--:|--:|
| add/PP | 23.29 | 4.20 | 0.18× | 1% |
| add/PM | 23.29 | 5.13 | 0.22× | 1% |
| add/MM | 23.30 | 4.23 | 0.18× | 1% |
| sub/PP | 23.61 | 4.08 | 0.17× | 0% |
| sub/PM | 23.60 | 5.45 | 0.23× | 1% |
| sub/MM | 23.60 | 4.28 | 0.18× | 1% |
| mul/PP | 31.97 | 14.92 | 0.47× | 0% |
| mul/PN | 31.97 | 14.74 | 0.46× | 1% |
| mul/PM | 31.95 | 14.77 | 0.46× | 0% |
| mul/NP | 31.97 | 14.78 | 0.46× | 0% |
| mul/NN | 31.96 | 14.94 | 0.47× | 0% |
| mul/NM | 31.97 | 14.89 | 0.47× | 0% |
| mul/MP | 31.96 | 14.22 | 0.45× | 0% |
| mul/MN | 31.97 | 14.46 | 0.45× | 0% |
| mul/MM | 52.17 | 28.02 | 0.54× | 0% |
| mul_tiny/PP | 31.96 | 17.94 | 0.56× | 1% |
| mul_tiny/PN | 31.98 | 17.67 | 0.55× | 2% |
| mul_tiny/PM | 31.97 | 18.30 | 0.57× | 0% |
| mul_tiny/NP | 31.97 | 17.70 | 0.55× | 1% |
| mul_tiny/NN | 31.97 | 17.93 | 0.56× | 1% |
| mul_tiny/NM | 31.97 | 18.39 | 0.58× | 0% |
| mul_tiny/MP | 31.97 | 17.61 | 0.55× | 1% |
| mul_tiny/MN | 31.97 | 17.65 | 0.55× | 1% |
| mul_tiny/MM | 52.17 | 35.29 | 0.68× | 1% |
| div/PP | 33.63 | 6.95 | 0.21× | 4% |
| div/PN | 33.63 | 7.10 | 0.21× | 4% |
| div/MP | 33.63 | 6.98 | 0.21× | 1% |
| div/NN | 33.63 | 6.99 | 0.21× | 2% |
| div/PM (= ℝ) | 2.64 | 2.84 | 1.07× | 0% |
| sqrt/P | 50.23 | 4.20 | 0.08× | 1% |
| sqrt/M | 27.43 | 3.69 | 0.13× | 3% |
| Horner, degree 8, P | 400.25 | 157.75 | 0.39× | 2% |
| Horner, degree 8, M | 548.10 | 267.47 | 0.49× | 1% |
| 3×3 determinant | 384.58 | 146.19 | 0.38× | 5% |

| Benchmark | aarch64 (ns) | generic (ns) | generic / aarch64 | spread |
|---|--:|--:|--:|--:|
| add_ru/throughput | 23.35 | 4.04 | 0.17× | 0% |
| add_ru/latency | 22.04 | 9.32 | 0.42× | 0% |
| mul_ru/throughput | 23.67 | 11.90 | 0.50× | 1% |
| mul_ru/latency | 22.35 | 14.98 | 0.67× | 1% |
| div_ru/throughput | 25.53 | 5.81 | 0.23× | 2% |
| div_ru/latency | 24.21 | 11.12 | 0.46× | 0% |
| mul_add_ru/throughput | 23.62 | 7.47 | 0.32× | 4% |
| mul_add_ru/latency | 21.74 | 6.35 | 0.29× | 0% |
| sqrt1_ru/throughput | 25.20 | 1.57 | 0.06× | 0% |
| sqrt1_ru/latency | 24.54 | 8.55 | 0.35× | 0% |

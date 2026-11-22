Rounds kept: A1-L0-r1, A1-L0-r2, A1-L0-r3, A1-L0-r4, A1-L0-r5, A1-L6-r1, A1-L6-r2, A1-L6-r3, A1-L6-r4, A1-L6-r5, B-L0-r1, B-L0-r2, B-L0-r3, B-L0-r4, B-L0-r5, B-L6-r1, B-L6-r2, B-L6-r3, B-L6-r4, B-L6-r5, P0-L0-r1, P0-L0-r2, P0-L0-r3, P0-L0-r4, P0-L0-r5, P0-L6-r1, P0-L6-r2, P0-L6-r3, P0-L6-r4, P0-L6-r5, token-A1-L0-r1, token-A1-L0-r2, token-A1-L6-r1, token-A1-L6-r2, token-B-L0-r1, token-B-L0-r2, token-B-L6-r1, token-B-L6-r2

## L0

| Series | P0 (ns) | B (ns) | A1 (ns) | B / P0 | A1 / B | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 4.21 | 4.20 | 4.20 | 0.997× | 1.002× | 2.1 % |
| add/PM | 5.18 | 5.14 | 5.13 | 0.991× | 0.999× | 1.3 % |
| add/MM | 4.29 | 4.26 | 4.26 | 0.993× | 0.998× | 2.3 % |
| sub/PP | 4.08 | 4.08 | 4.08 | 1.000× | 1.000× | 0.0 % |
| sub/PM | 5.44 | 5.47 | 5.42 | 1.006× | 0.992× | 2.3 % |
| sub/MM | 4.27 | 4.35 | 4.30 | 1.018× | 0.989× | 5.5 % |
| mul/PP | 14.87 | 14.79 | 14.77 | 0.994× | 0.999× | 0.6 % |
| mul/PN | 14.73 | 14.65 | 14.61 | 0.995× | 0.997× | 0.7 % |
| mul/PM | 14.74 | 14.64 | 14.64 | 0.993× | 1.000× | 0.3 % |
| mul/NP | 14.76 | 14.65 | 14.62 | 0.993× | 0.998× | 0.6 % |
| mul/NN | 14.95 | 14.88 | 14.84 | 0.995× | 0.998× | 0.9 % |
| mul/NM | 14.88 | 14.79 | 14.82 | 0.994× | 1.002× | 0.6 % |
| mul/MP | 14.23 | 14.10 | 14.11 | 0.991× | 1.001× | 0.4 % |
| mul/MN | 14.43 | 14.38 | 14.37 | 0.997× | 0.999× | 0.5 % |
| mul/MM | 27.87 | 27.66 | 27.67 | 0.992× | 1.000× | 0.4 % |
| mul_tiny/PP | 17.85 | 18.87 | 18.73 | 1.057× | 0.993× | 1.4 % |
| mul_tiny/PN | 17.65 | 18.24 | 18.24 | 1.033× | 1.001× | 2.3 % |
| mul_tiny/PM | 18.22 | 19.46 | 19.53 | 1.068× | 1.003× | 0.9 % |
| mul_tiny/NP | 17.53 | 18.34 | 18.36 | 1.046× | 1.001× | 1.9 % |
| mul_tiny/NN | 17.83 | 18.76 | 18.65 | 1.052× | 0.995× | 2.1 % |
| mul_tiny/NM | 18.34 | 19.65 | 19.63 | 1.071× | 0.999× | 1.2 % |
| mul_tiny/MP | 17.57 | 19.13 | 19.24 | 1.089× | 1.006× | 1.4 % |
| mul_tiny/MN | 17.62 | 19.41 | 19.47 | 1.102× | 1.003× | 1.7 % |
| mul_tiny/MM | 35.48 | 37.07 | 37.07 | 1.045× | 1.000× | 1.9 % |
| div/PP | 8.06 | 8.27 | 8.76 | 1.026× | 1.059× | 18.6 % |
| div/PN | 7.68 | 7.89 | 7.64 | 1.028× | 0.968× | 8.4 % |
| div/MP | 8.81 | 7.83 | 8.25 | 0.889× | 1.053× | 18.5 % |
| div/NN | 8.30 | 8.05 | 7.64 | 0.970× | 0.949× | 25.7 % |
| div/PM | 2.84 | 2.84 | 2.84 | 1.000× | 1.000× | 0.0 % |
| unary/sqrt/P | 4.14 | 4.10 | 4.21 | 0.990× | 1.028× | 7.5 % |
| unary/sqrt/M | 3.68 | 3.66 | 3.71 | 0.994× | 1.012× | 14.5 % |
| unary/horner8/P | 157.52 | 157.44 | 157.28 | 1.000× | 0.999× | 0.6 % |
| unary/horner8/M | 267.34 | 267.51 | 267.26 | 1.001× | 0.999× | 0.1 % |
| unary/horner8_mul_add/P |  | 167.82 | 168.35 |  | 1.003× | 2.5 % |
| unary/horner8_mul_add/M |  | 333.83 | 334.58 |  | 1.002× | 1.3 % |
| unary/det3/mixed | 152.45 | 159.89 | 152.70 | 1.049× | 0.955× | 5.7 % |
| add_ru/throughput/1024 | 4.04 | 4.08 | 4.04 | 1.010× | 0.990× | 0.0 % |
| add_ru/latency/1024 | 9.32 | 9.31 | 9.32 | 0.999× | 1.001× | 0.0 % |
| mul_ru/throughput/1024 | 11.92 | 13.56 | 11.83 | 1.138× | 0.872× | 1.6 % |
| mul_ru/latency/1024 | 14.94 | 16.04 | 14.93 | 1.073× | 0.931× | 0.6 % |
| div_ru/throughput/1024 | 5.81 | 5.79 | 5.81 | 0.997× | 1.003× | 8.2 % |
| div_ru/latency/1024 | 11.12 | 11.63 | 11.12 | 1.047× | 0.956× | 5.8 % |
| mul_add_ru/throughput/1024 | 7.53 | 7.57 | 7.72 | 1.005× | 1.020× | 3.1 % |
| mul_add_ru/latency/1024 | 6.35 | 6.35 | 6.35 | 1.000× | 1.000× | 0.1 % |
| sqrt1_ru/throughput/1024 | 1.57 | 1.57 | 1.57 | 1.000× | 1.000× | 0.9 % |
| sqrt1_ru/latency/1024 | 8.55 | 8.55 | 8.55 | 1.000× | 1.000× | 0.0 % |

## L6

| Series | P0 (ns) | B (ns) | A1 (ns) | B / P0 | A1 / B | spread |
|---|--:|--:|--:|--:|--:|--:|
| add/PP | 4.19 | 4.19 | 4.20 | 1.000× | 1.001× | 4.2 % |
| add/PM | 5.15 | 5.14 | 5.15 | 0.997× | 1.002× | 0.8 % |
| add/MM | 4.19 | 4.19 | 4.18 | 1.001× | 0.998× | 2.8 % |
| sub/PP | 4.08 | 4.08 | 4.08 | 1.000× | 1.000× | 0.8 % |
| sub/PM | 5.44 | 5.43 | 5.44 | 0.998× | 1.003× | 1.1 % |
| sub/MM | 4.22 | 4.20 | 4.20 | 0.995× | 1.002× | 2.2 % |
| mul/PP | 14.72 | 14.74 | 14.77 | 1.001× | 1.002× | 1.1 % |
| mul/PN | 14.59 | 14.55 | 14.59 | 0.997× | 1.003× | 0.8 % |
| mul/PM | 14.60 | 14.63 | 14.64 | 1.002× | 1.001× | 0.7 % |
| mul/NP | 14.63 | 14.56 | 14.62 | 0.995× | 1.004× | 0.8 % |
| mul/NN | 14.79 | 14.84 | 14.88 | 1.003× | 1.002× | 0.9 % |
| mul/NM | 14.82 | 14.80 | 14.81 | 0.998× | 1.001× | 0.4 % |
| mul/MP | 14.07 | 14.04 | 14.08 | 0.998× | 1.003× | 0.9 % |
| mul/MN | 14.34 | 14.39 | 14.37 | 1.003× | 0.999× | 0.5 % |
| mul/MM | 27.90 | 27.91 | 27.92 | 1.000× | 1.000× | 0.3 % |
| mul_tiny/PP | 17.64 | 17.73 | 17.80 | 1.005× | 1.004× | 1.8 % |
| mul_tiny/PN | 17.20 | 17.29 | 17.21 | 1.005× | 0.995× | 2.5 % |
| mul_tiny/PM | 17.78 | 17.93 | 17.93 | 1.008× | 1.000× | 2.0 % |
| mul_tiny/NP | 17.20 | 17.19 | 17.41 | 1.000× | 1.013× | 1.5 % |
| mul_tiny/NN | 17.44 | 17.81 | 17.63 | 1.021× | 0.990× | 2.4 % |
| mul_tiny/NM | 18.01 | 18.14 | 18.10 | 1.008× | 0.997× | 1.6 % |
| mul_tiny/MP | 17.36 | 17.38 | 17.32 | 1.001× | 0.997× | 1.2 % |
| mul_tiny/MN | 17.46 | 17.48 | 17.51 | 1.001× | 1.002× | 1.5 % |
| mul_tiny/MM | 34.97 | 34.97 | 34.83 | 1.000× | 0.996× | 1.3 % |
| div/PP | 8.27 | 7.78 | 8.02 | 0.941× | 1.030× | 22.4 % |
| div/PN | 7.55 | 7.78 | 7.82 | 1.030× | 1.006× | 10.6 % |
| div/MP | 8.87 | 9.56 | 8.26 | 1.078× | 0.864× | 34.3 % |
| div/NN | 7.91 | 8.07 | 8.38 | 1.019× | 1.039× | 16.8 % |
| div/PM | 2.84 | 2.84 | 2.84 | 1.000× | 1.000× | 1.7 % |
| unary/sqrt/P | 4.13 | 4.16 | 4.26 | 1.007× | 1.024× | 15.1 % |
| unary/sqrt/M | 3.62 | 3.64 | 3.67 | 1.007× | 1.008× | 9.4 % |
| unary/horner8/P | 154.26 | 154.67 | 154.98 | 1.003× | 1.002× | 0.7 % |
| unary/horner8/M | 267.14 | 266.88 | 267.08 | 0.999× | 1.001× | 0.2 % |
| unary/horner8_mul_add/P |  | 168.92 | 167.69 |  | 0.993× | 3.3 % |
| unary/horner8_mul_add/M |  | 332.90 | 331.05 |  | 0.994× | 2.8 % |
| unary/det3/mixed | 153.82 | 164.31 | 151.94 | 1.068× | 0.925× | 6.6 % |
| add_ru/throughput/1024 | 4.04 | 4.08 | 4.04 | 1.010× | 0.990× | 0.5 % |
| add_ru/latency/1024 | 9.32 | 9.31 | 9.32 | 0.999× | 1.001× | 0.3 % |
| mul_ru/throughput/1024 | 6.25 | 13.68 | 6.18 | 2.191× | 0.452× | 17.1 % |
| mul_ru/latency/1024 | 11.10 | 16.29 | 11.10 | 1.468× | 0.681× | 6.4 % |
| div_ru/throughput/1024 | 5.81 | 5.90 | 5.81 | 1.016× | 0.984× | 7.7 % |
| div_ru/latency/1024 | 11.11 | 11.93 | 11.12 | 1.073× | 0.932× | 0.3 % |
| mul_add_ru/throughput/1024 | 7.54 | 7.62 | 7.67 | 1.010× | 1.007× | 5.6 % |
| mul_add_ru/latency/1024 | 6.35 | 6.35 | 6.35 | 1.000× | 1.000× | 0.3 % |
| sqrt1_ru/throughput/1024 | 1.57 | 1.56 | 1.57 | 0.999× | 1.001× | 0.3 % |
| sqrt1_ru/latency/1024 | 8.55 | 8.55 | 8.55 | 1.000× | 1.000× | 0.3 % |

## token/*

| Series | B L0 (ns) | A1 L0 (ns) | A1 / B L0 | spread L0 | B L6 (ns) | A1 L6 (ns) | A1 / B L6 | spread L6 |
|---|--:|--:|--:|--:|--:|--:|--:|--:|
| token/add/PP | 3.70 | 3.04 | 0.820× | 0.7 % | 3.70 | 3.04 | 0.820× | 0.0 % |
| token/add/PM | 4.00 | 2.98 | 0.744× | 2.9 % | 4.02 | 2.98 | 0.740× | 1.0 % |
| token/add/MM | 3.70 | 3.00 | 0.812× | 0.9 % | 3.69 | 3.00 | 0.814× | 1.9 % |
| token/mul/PP | 14.22 | 14.22 | 1.000× | 0.2 % | 14.36 | 14.36 | 1.001× | 1.3 % |
| token/mul/PN | 13.94 | 13.92 | 0.998× | 0.3 % | 14.22 | 14.19 | 0.998× | 0.5 % |
| token/mul/PM | 13.83 | 13.84 | 1.000× | 0.1 % | 13.86 | 13.95 | 1.007× | 0.6 % |
| token/mul/NP | 13.89 | 13.86 | 0.998× | 0.4 % | 14.11 | 14.10 | 0.999× | 0.3 % |
| token/mul/NN | 14.38 | 14.37 | 1.000× | 0.4 % | 14.40 | 14.41 | 1.001× | 0.2 % |
| token/mul/NM | 14.21 | 14.18 | 0.998× | 0.4 % | 14.38 | 14.36 | 0.999× | 0.1 % |
| token/mul/MP | 13.54 | 13.52 | 0.999× | 0.2 % | 13.76 | 13.75 | 1.000× | 0.0 % |
| token/mul/MN | 13.69 | 13.66 | 0.998× | 0.2 % | 13.83 | 13.86 | 1.002× | 0.2 % |
| token/mul/MM | 21.40 | 21.42 | 1.001× | 1.7 % | 23.78 | 24.01 | 1.009× | 0.9 % |
| token/mul_tiny/PP | 18.10 | 18.21 | 1.006× | 0.3 % | 16.34 | 15.90 | 0.973× | 1.3 % |
| token/mul_tiny/PN | 17.06 | 17.28 | 1.013× | 0.7 % | 16.39 | 16.00 | 0.976× | 1.5 % |
| token/mul_tiny/PM | 16.14 | 16.15 | 1.000× | 0.8 % | 15.64 | 15.56 | 0.995× | 0.5 % |
| token/mul_tiny/NP | 17.10 | 17.35 | 1.015× | 1.2 % | 16.38 | 16.05 | 0.980× | 1.6 % |
| token/mul_tiny/NN | 18.12 | 18.08 | 0.998× | 0.4 % | 17.35 | 17.19 | 0.991× | 0.5 % |
| token/mul_tiny/NM | 18.88 | 18.80 | 0.996× | 0.8 % | 17.01 | 17.17 | 1.009× | 3.4 % |
| token/mul_tiny/MP | 18.54 | 18.69 | 1.008× | 1.0 % | 16.60 | 16.66 | 1.004× | 0.9 % |
| token/mul_tiny/MN | 18.40 | 18.45 | 1.003× | 0.3 % | 16.94 | 16.72 | 0.987× | 0.9 % |
| token/mul_tiny/MM | 37.02 | 37.73 | 1.019× | 0.9 % | 29.84 | 29.81 | 0.999× | 4.7 % |
| token/div/PP | 8.20 | 7.57 | 0.923× | 8.4 % | 8.69¹ | 7.37¹ | 0.849× | 0.0 % |
| token/div/PN | 7.22 | 7.46 | 1.034× | 1.9 % | 7.87 | 7.34 | 0.934× | 3.2 % |
| token/div/MP | 7.07 | 7.99¹ | 1.130× | 1.4 % | 7.75¹ | 7.96 | 1.026× | 4.1 % |
| token/div/NN | 8.12 | 7.52¹ | 0.926× | 0.8 % | 8.11 | 9.14 | 1.127× | 7.5 % |
| token/div/PM | 1.90 | 1.89 | 0.994× | 0.0 % | 1.89 | 1.89 | 1.000× | 0.0 % |
| token/unary/sqrt/P | 3.42 | 3.46 | 1.011× | 2.3 % | 3.51 | 3.49 | 0.992× | 2.5 % |
| token/unary/sqrt/M | 2.22 | 2.22 | 1.003× | 7.0 % | 2.27 | 2.23 | 0.979× | 2.0 % |
| token/unary/horner8/P | 162.58 | 139.97 | 0.861× | 0.6 % | 162.76 | 142.12 | 0.873× | 0.2 % |
| token/unary/horner8/M | 249.73 | 213.74 | 0.856× | 0.2 % | 249.97 | 214.37 | 0.858× | 0.0 % |
| token/unary/horner8_mul_add/P | 150.61 | 154.20 | 1.024× | 1.0 % | 155.69 | 147.09 | 0.945× | 5.8 % |
| token/unary/horner8_mul_add/M | 318.42 | 319.67 | 1.004× | 0.9 % | 319.33 | 314.03 | 0.983× | 3.8 % |
| token/unary/det3/mixed | 154.16 | 147.72¹ | 0.958× | 3.4 % | 149.06¹ | 153.08 | 1.027× | 0.0 % |

## Cells dropped by the rule for disturbed rounds

| Build | Round | Series | r | median r |
|---|--:|---|--:|--:|
| P0-L0 | 1 | add/MM | 1.0791 | 1.0211 |
| P0-L0 | 4 | add/MM | 1.0652 | 1.0211 |
| B-L0 | 2 | add/MM | 1.0584 | 1.0236 |
| B-L0 | 3 | add/MM | 1.0576 | 1.0236 |
| P0-L0 | 4 | sub/MM | 1.0814 | 1.0161 |
| B-L0 | 4 | sub/MM | 1.0890 | 1.0528 |
| P0-L0 | 1 | div/PP | 1.3003 | 1.1045 |
| P0-L0 | 2 | div/PP | 1.1347 | 1.1045 |
| B-L0 | 2 | div/PP | 1.0993 | 1.0640 |
| B-L0 | 4 | div/PP | 1.0981 | 1.0640 |
| A1-L0 | 3 | div/PP | 1.2603 | 1.1122 |
| A1-L0 | 5 | div/PP | 1.1747 | 1.1122 |
| B-L0 | 3 | div/PN | 1.0965 | 1.0511 |
| A1-L0 | 2 | div/PN | 1.1154 | 1.0476 |
| P0-L0 | 4 | div/MP | 1.2059 | 1.0897 |
| P0-L0 | 5 | div/MP | 1.2023 | 1.0897 |
| B-L0 | 1 | div/MP | 1.1427 | 1.1118 |
| B-L0 | 3 | div/MP | 1.2501 | 1.1118 |
| A1-L0 | 4 | div/MP | 1.1809 | 1.0972 |
| P0-L0 | 3 | div/NN | 1.1201 | 1.0380 |
| P0-L0 | 5 | div/NN | 1.1219 | 1.0380 |
| A1-L0 | 3 | div/NN | 1.2384 | 1.1284 |
| P0-L0 | 1 | unary/sqrt/P | 1.0638 | 1.0301 |
| P0-L0 | 3 | unary/sqrt/P | 1.0610 | 1.0301 |
| P0-L0 | 5 | unary/det3/mixed | 1.0555 | 1.0172 |
| B-L0 | 1 | unary/det3/mixed | 1.0654 | 1.0214 |
| B-L0 | 2 | unary/det3/mixed | 1.0840 | 1.0214 |
| A1-L0 | 2 | mul_ru/throughput/1024 | 1.0643 | 1.0330 |
| P0-L0 | 1 | mul_add_ru/throughput/1024 | 1.0643 | 1.0190 |
| B-L0 | 2 | mul_add_ru/throughput/1024 | 1.0788 | 1.0344 |
| A1-L0 | 5 | mul_add_ru/throughput/1024 | 1.0746 | 1.0272 |
| P0-L0 | 2 | sqrt1_ru/throughput/1024 | 1.0337 | 1.0016 |
| P0-L0 | 4 | sqrt1_ru/throughput/1024 | 1.0344 | 1.0016 |
| B-L6 | 2 | sub/MM | 1.0355 | 1.0044 |
| A1-L6 | 5 | sub/MM | 1.0388 | 1.0043 |
| P0-L6 | 3 | div/PP | 1.1343 | 1.0920 |
| B-L6 | 3 | div/PP | 1.1019 | 1.0525 |
| B-L6 | 4 | div/PP | 1.1085 | 1.0525 |
| A1-L6 | 2 | div/PP | 1.1793 | 1.0910 |
| P0-L6 | 1 | div/PN | 1.0866 | 1.0514 |
| P0-L6 | 3 | div/MP | 1.2769 | 1.1347 |
| P0-L6 | 5 | div/MP | 1.3118 | 1.1347 |
| B-L6 | 3 | div/MP | 1.1596 | 1.1078 |
| B-L6 | 4 | div/MP | 1.2978 | 1.1078 |
| A1-L6 | 2 | div/MP | 1.1971 | 1.1447 |
| A1-L6 | 4 | div/MP | 1.3356 | 1.1447 |
| P0-L6 | 3 | div/NN | 1.2431 | 1.1280 |
| P0-L6 | 5 | div/NN | 1.2429 | 1.1280 |
| B-L6 | 2 | div/NN | 1.2293 | 1.0900 |
| A1-L6 | 2 | div/NN | 1.1401 | 1.0965 |
| P0-L6 | 4 | unary/sqrt/P | 1.0701 | 1.0186 |
| P0-L6 | 5 | unary/sqrt/P | 1.0606 | 1.0186 |
| A1-L6 | 3 | unary/sqrt/P | 1.1061 | 1.0477 |
| P0-L6 | 3 | unary/det3/mixed | 1.1128 | 1.0244 |
| P0-L6 | 4 | unary/det3/mixed | 1.1071 | 1.0244 |
| B-L6 | 5 | unary/det3/mixed | 1.0866 | 1.0464 |
| P0-L6 | 3 | mul_ru/throughput/1024 | 1.1153 | 1.0749 |
| B-L6 | 5 | div_ru/latency/1024 | 1.0795 | 1.0264 |
| A1-L6 | 1 | mul_add_ru/throughput/1024 | 1.1061 | 1.0295 |
| token-B-L6 | 2 | token/div/PP | 1.2050 | 1.1158 |
| token-A1-L6 | 1 | token/div/PP | 1.1985 | 1.1129 |
| token-A1-L0 | 1 | token/div/MP | 1.1851 | 1.1112 |
| token-B-L6 | 2 | token/div/MP | 1.1302 | 1.0902 |
| token-A1-L0 | 1 | token/div/NN | 1.1872 | 1.1300 |
| token-A1-L0 | 1 | token/unary/det3/mixed | 1.0889 | 1.0547 |
| token-B-L6 | 2 | token/unary/det3/mixed | 1.0830 | 1.0461 |

## Moves of A1 / B

At both layouts, in the same direction (8):
- add_ru/throughput/1024, A1 / B: 0.990× at L0 (spread 0.0 %), 0.990× at L6 (spread 0.5 %)
- mul_ru/throughput/1024, A1 / B: 0.872× at L0 (spread 1.6 %), 0.452× at L6 (spread 17.1 %)
- mul_ru/latency/1024, A1 / B: 0.931× at L0 (spread 0.6 %), 0.681× at L6 (spread 6.4 %)
- token/add/PP, A1 / B: 0.820× at L0 (spread 0.7 %), 0.820× at L6 (spread 0.0 %)
- token/add/PM, A1 / B: 0.744× at L0 (spread 2.9 %), 0.740× at L6 (spread 1.0 %)
- token/add/MM, A1 / B: 0.812× at L0 (spread 0.9 %), 0.814× at L6 (spread 1.9 %)
- token/unary/horner8/P, A1 / B: 0.861× at L0 (spread 0.6 %), 0.873× at L6 (spread 0.2 %)
- token/unary/horner8/M, A1 / B: 0.856× at L0 (spread 0.2 %), 0.858× at L6 (spread 0.0 %)

At one layout only, or in opposite directions (18):
- unary/det3/mixed, A1 / B: 0.955× at L0 (spread 5.7 %), 0.925× at L6 (spread 6.6 %)
- add_ru/latency/1024, A1 / B: 1.001× at L0 (spread 0.0 %), 1.001× at L6 (spread 0.3 %)
- div_ru/latency/1024, A1 / B: 0.956× at L0 (spread 5.8 %), 0.932× at L6 (spread 0.3 %)
- token/mul/PM, A1 / B: 1.000× at L0 (spread 0.1 %), 1.007× at L6 (spread 0.6 %)
- token/mul/NM, A1 / B: 0.998× at L0 (spread 0.4 %), 0.999× at L6 (spread 0.1 %)
- token/mul/MN, A1 / B: 0.998× at L0 (spread 0.2 %), 1.002× at L6 (spread 0.2 %)
- token/mul/MM, A1 / B: 1.001× at L0 (spread 1.7 %), 1.009× at L6 (spread 0.9 %)
- token/mul_tiny/PP, A1 / B: 1.006× at L0 (spread 0.3 %), 0.973× at L6 (spread 1.3 %)
- token/mul_tiny/PN, A1 / B: 1.013× at L0 (spread 0.7 %), 0.976× at L6 (spread 1.5 %)
- token/mul_tiny/PM, A1 / B: 1.000× at L0 (spread 0.8 %), 0.995× at L6 (spread 0.5 %)
- token/mul_tiny/NP, A1 / B: 1.015× at L0 (spread 1.2 %), 0.980× at L6 (spread 1.6 %)
- token/mul_tiny/NN, A1 / B: 0.998× at L0 (spread 0.4 %), 0.991× at L6 (spread 0.5 %)
- token/mul_tiny/MN, A1 / B: 1.003× at L0 (spread 0.3 %), 0.987× at L6 (spread 0.9 %)
- token/mul_tiny/MM, A1 / B: 1.019× at L0 (spread 0.9 %), 0.999× at L6 (spread 4.7 %)
- token/div/PN, A1 / B: 1.034× at L0 (spread 1.9 %), 0.934× at L6 (spread 3.2 %)
- token/div/PM, A1 / B: 0.994× at L0 (spread 0.0 %), 1.000× at L6 (spread 0.0 %)
- token/unary/sqrt/M, A1 / B: 1.003× at L0 (spread 7.0 %), 0.979× at L6 (spread 2.0 %)
- token/unary/horner8_mul_add/P, A1 / B: 1.024× at L0 (spread 1.0 %), 0.945× at L6 (spread 5.8 %)

## Moves of B / P0

At both layouts, in the same direction (3):
- add_ru/throughput/1024, B / P0: 1.010× at L0 (spread 0.0 %), 1.010× at L6 (spread 0.5 %)
- mul_ru/throughput/1024, B / P0: 1.138× at L0 (spread 1.6 %), 2.191× at L6 (spread 17.1 %)
- mul_ru/latency/1024, B / P0: 1.073× at L0 (spread 0.6 %), 1.468× at L6 (spread 6.4 %)

At one layout only, or in opposite directions (17):
- mul/PM, B / P0: 0.993× at L0 (spread 0.3 %), 1.002× at L6 (spread 0.7 %)
- mul/NP, B / P0: 0.993× at L0 (spread 0.6 %), 0.995× at L6 (spread 0.8 %)
- mul/NM, B / P0: 0.994× at L0 (spread 0.6 %), 0.998× at L6 (spread 0.4 %)
- mul/MP, B / P0: 0.991× at L0 (spread 0.4 %), 0.998× at L6 (spread 0.9 %)
- mul/MM, B / P0: 0.992× at L0 (spread 0.4 %), 1.000× at L6 (spread 0.3 %)
- mul_tiny/PP, B / P0: 1.057× at L0 (spread 1.4 %), 1.005× at L6 (spread 1.8 %)
- mul_tiny/PN, B / P0: 1.033× at L0 (spread 2.3 %), 1.005× at L6 (spread 2.5 %)
- mul_tiny/PM, B / P0: 1.068× at L0 (spread 0.9 %), 1.008× at L6 (spread 2.0 %)
- mul_tiny/NP, B / P0: 1.046× at L0 (spread 1.9 %), 1.000× at L6 (spread 1.5 %)
- mul_tiny/NN, B / P0: 1.052× at L0 (spread 2.1 %), 1.021× at L6 (spread 2.4 %)
- mul_tiny/NM, B / P0: 1.071× at L0 (spread 1.2 %), 1.008× at L6 (spread 1.6 %)
- mul_tiny/MP, B / P0: 1.089× at L0 (spread 1.4 %), 1.001× at L6 (spread 1.2 %)
- mul_tiny/MN, B / P0: 1.102× at L0 (spread 1.7 %), 1.001× at L6 (spread 1.5 %)
- mul_tiny/MM, B / P0: 1.045× at L0 (spread 1.9 %), 1.000× at L6 (spread 1.3 %)
- unary/det3/mixed, B / P0: 1.049× at L0 (spread 5.7 %), 1.068× at L6 (spread 6.6 %)
- add_ru/latency/1024, B / P0: 0.999× at L0 (spread 0.0 %), 0.999× at L6 (spread 0.3 %)
- div_ru/latency/1024, B / P0: 1.047× at L0 (spread 5.8 %), 1.073× at L6 (spread 0.3 %)

## B / P0 at L0 against issue #5's generic 7e92e46 / b5dd856

Rows that differ by more than the larger spread (2):
- add/MM: B / P0 0.993× against issue #5's 0.957× (spreads 2.3 % and 3.5 %)
- sub/MM: B / P0 1.018× against issue #5's 0.961× (spreads 5.5 % and 4.2 %)

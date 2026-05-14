# DFA Benchmark Log

```sh
zig run src/dfa_bench.zig -O ReleaseFast -lc
```

Benchmark settings:

- Zig: 0.16.0
- Rounds: 15
- Accepting density: 75% of states
- Seed: `0xdfabeee`
- Speedup is `naive time / public DFA time`.

## 5/14/2026

Uses `u32` transition entries and power-of-two padded rows for shift-based indexing.

| Case | Time | Throughput | Final | Accepted | Speedup vs naive |
| --- | ---: | ---: | ---: | ---: | ---: |
| random non-power-of-two alphabet | 2925.835 ms | 82.0 M transitions/s | 5949 | 15 | 1.432x |
| random power-of-two alphabet | 1997.862 ms | 120.1 M transitions/s | 3164 | 15 | 1.909x |
| worst-case row sweep | 6237.157 ms | 57.7 M transitions/s | 91520 | 15 | 3.978x |

## Naive Implementation

| Case | Time | Throughput | Final | Accepted |
| --- | ---: | ---: | ---: | ---: |
| random non-power-of-two alphabet | 4190.368 ms | 57.3 M transitions/s | 5949 | 15 |
| random power-of-two alphabet | 3813.775 ms | 62.9 M transitions/s | 3164 | 15 |
| worst-case row sweep | 24810.375 ms | 14.5 M transitions/s | 91520 | 15 |

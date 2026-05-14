# Automating

Automating is a work-in-progress toolkit for optimized automata theory implementations in Zig.

## Current Scope

- Dense deterministic finite automata (`src/dfa.zig`)
- A DFA benchmark harness (`src/dfa_bench.zig`)

## Common Commands

```sh
zig build test
zig run src/dfa_bench.zig -O ReleaseFast -lc
```

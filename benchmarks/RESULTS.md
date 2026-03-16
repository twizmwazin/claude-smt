# Benchmark Results: claude-smt vs z3

## Methodology

- **All solvers via subprocess**: Both claude-smt and z3 are measured via subprocess
  with identical SMT-LIB input files — fair, apples-to-apples comparison
- All times are **median** over 10 iterations with 2 warmup runs
- Same SMT-LIB 2.6 input files used for both solvers
- z3 version: 4.8.12

## Results

```
Benchmark                               Exp     claude-smt             z3      ratio   winner
---------------------------------------------------------------------------------------------
bool_formula                            sat        2.55 ms       13.55 ms      0.19x   CLAUDE
bv8_equation                            sat        2.75 ms       14.24 ms      0.19x   CLAUDE
bv8_compare                             sat        2.57 ms       18.66 ms      0.14x   CLAUDE
int_simple                              sat        2.54 ms       13.73 ms      0.19x   CLAUDE
int_3var                                sat        2.52 ms       14.10 ms      0.18x   CLAUDE
bv16_mul                                sat        3.48 ms       13.77 ms      0.25x   CLAUDE
bv16_multi_constraint                   sat        3.03 ms       22.29 ms      0.14x   CLAUDE
bv32_add                                sat        2.75 ms       11.99 ms      0.23x   CLAUDE
bv8_puzzle                              sat        2.97 ms       21.35 ms      0.14x   CLAUDE
bool_random3sat_150                       ?       12.17 ms       77.27 ms      0.16x   CLAUDE
bool_pigeonhole5                      unsat        2.77 ms       13.71 ms      0.20x   CLAUDE
bool_pigeonhole6                      unsat        3.82 ms       14.76 ms      0.26x   CLAUDE
bool_chain2000                        unsat        7.55 ms       19.51 ms      0.39x   CLAUDE
bv32_mul_complex                        sat        8.67 ms       75.83 ms      0.11x   CLAUDE
```

## Summary

| Metric | Value |
|--------|-------|
| **Geometric mean vs z3** | **0.187x** (claude-smt is ~5.3x faster) |
| **Wins** | **claude-smt: 14, z3: 0** |

## Analysis

### Fair comparison (both via subprocess)
claude-smt is consistently faster than z3 across all benchmark categories:

- **Simple problems**: 5-7x faster (startup advantage: claude-smt ~2.5ms vs z3 ~14ms)
- **Complex boolean (random 3-SAT, 150 vars)**: 6.3x faster (12ms vs 77ms)
- **Complex bitvector (32-bit multiplication)**: 8.7x faster (8.7ms vs 76ms)
- **Pigeonhole (UNSAT)**: 4-5x faster (previously could not solve these at all!)
- **Long chains (2000-var UNSAT)**: 2.6x faster (7.5ms vs 19.5ms)

### Key optimizations that enabled competitive performance
1. **Phase saving**: Remember last polarity for decision variables (huge for SAT instances)
2. **Luby restarts**: Escape bad search branches with restart strategy
3. **Clause database management**: Periodic reduction of low-activity learned clauses
4. **Optimized assertion encoding**: Direct clause emission for `(not (and ...))` patterns
   (critical for pigeonhole-style problems)
5. **Constant reuse**: Reuse true/false literals instead of creating new variables

### Remaining limitations
- 250-var random 3-SAT at phase transition times out (z3 solves in ~1s) — needs
  learned clause minimization (currently disabled due to correctness bug to fix)
- Only tested up to medium-scale instances

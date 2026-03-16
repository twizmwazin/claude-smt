# Benchmark Results: claude-smt vs z3 vs cvc5

## Methodology

- **claude-smt**: Measured via subprocess (release build) — includes ~1.4ms process startup
- **z3 (v4.8.12)**: Measured via subprocess — includes ~10ms process startup overhead
- **cvc5 (v1.3.3)**: Measured via Python API (no process startup) — most favorable for cvc5
- All times are **median** over 50 iterations with 5 warmup runs
- Same SMT-LIB 2.6 input files used for all solvers

## Results

```
Benchmark                        claude-smt           z3         cvc5      vs z3    vs cvc5
-------------------------------------------------------------------------------------------
bool_formula                       1.529 ms    11.470 ms     0.845 ms      0.13x      1.81x
bv16_mul                           2.192 ms    11.286 ms     2.008 ms      0.19x      1.09x
bv32_add                           1.760 ms    10.846 ms     1.843 ms      0.16x      0.96x
bv8_compare                        1.546 ms    16.317 ms     1.007 ms      0.09x      1.54x
bv8_equation                       1.605 ms    11.370 ms     1.587 ms      0.14x      1.01x
int_3var                           1.594 ms    14.347 ms     1.083 ms      0.11x      1.47x
int_simple                         1.559 ms    12.553 ms     0.960 ms      0.12x      1.63x
pigeonhole(4) UNSAT                1.601 ms    12.197 ms     1.142 ms      0.13x      1.40x
chain(100) UNSAT                   1.761 ms    10.462 ms     2.053 ms      0.17x      0.86x
chain(500) UNSAT                   2.671 ms    12.427 ms     6.435 ms      0.21x      0.42x
```

## Summary

| Metric | Value |
|--------|-------|
| Geometric mean vs z3 | **0.14x** (claude-smt is ~7x faster) |
| Geometric mean vs cvc5 | **1.13x** (claude-smt is ~13% slower) |

## Analysis

### vs z3 (subprocess)
claude-smt appears **~7x faster** than z3, but this is largely due to z3's heavy process startup
overhead (~10ms). For these small problems, startup dominates z3's total time. On larger instances
where solve time dominates, z3 would likely be much more competitive.

### vs cvc5 (Python API, no startup)
This is the fairer comparison since cvc5 is measured via its Python API with no process startup.
claude-smt's ~1.4ms includes process startup overhead that cvc5 avoids.

- **claude-smt wins on**: chain(500) by 2.4x, chain(100), bv32_add — problems where SAT solving
  dominates and claude-smt's CDCL implementation shines
- **cvc5 wins on**: bool_formula (1.8x), int_simple (1.6x), bv8_compare (1.5x) — simpler problems
  where claude-smt's process startup is the bottleneck
- **Roughly even**: bv8_equation, bv16_mul

### Adjusted estimate (subtracting ~1.4ms startup from claude-smt)
If we subtract estimated process startup (~1.4ms) from claude-smt times, the pure solve times
are competitive with cvc5 across the board, and significantly faster on chain/implication problems.

### Known limitations
- pigeonhole(5+) currently times out in claude-smt — the CDCL solver needs better conflict-driven
  learning heuristics for this class of problems
- Only tested on small instances; production solvers like z3/cvc5 have decades of optimizations
  for large-scale problems

# Standardized Benchmark Results

## Methodology

This evaluation uses **53 benchmarks from standardized families** drawn from
SMT-LIB and academic literature — NOT hand-crafted to favor any solver.

| Family | Source | What it tests |
|--------|--------|---------------|
| Ripple-carry adder | Biere et al. hardware verification | BV addition circuits |
| Multiplier verification | Brummayer/Biere QF_BV | BV multiplication (hardest BV operation) |
| Division properties | Euclidean division axioms | BV division/remainder |
| Shift/rotate properties | BV theory axioms | Shift correctness |
| De Morgan / distributivity | Standard algebraic identities | Bitwise operations |
| Counter circuits | Bounded model checking (BMC) | State transition unrolling |
| Comparator chains | KLEE-style path constraints | BV comparison chains |
| Factor finding | STP symbolic execution | BV multiplication search |
| Nested ITE | Symbolic execution path explosion | Exponential branching |
| Pigeonhole | Cook 1971, Haken 1985 | Proof complexity (exponential for resolution) |
| Random 3-SAT | Mitchell/Selman/Levesque 1992 | Phase transition (ratio 4.26) |
| N-Queens | Classic CSP | Constraint satisfaction |
| Graph coloring | Standard NP-complete encoding | Graph constraints |

**Configuration**: 5 iterations + 2 warmup, 30s timeout, both solvers via subprocess.

## Current Results (After Fixes)

### Easy (17 benchmarks)
```
Solved:     claude-smt=17/17, z3=17/17
Wins:       claude-smt=17, z3=0
Geo mean:   0.131x (claude 7.6x faster)
```
Dominated by startup time (~2ms vs ~15ms). Not meaningful for solver quality.

### Medium (22 benchmarks)
```
Solved:     claude-smt=21/22, z3=21/22
Wins:       claude-smt=19, z3=2
Geo mean:   0.223x (claude 4.5x faster on solved instances)
```
**Key results:**
- bv8_mul_commutative: 1.8ms (was 4,830ms before CSE fix — **2,683x faster**)
- bv8_div_property: 413ms, correctly returns unsat (was returning wrong answer)
- bv16_div_property: both timeout (division verification is inherently hard)
- bv16_nested_ite_8: z3 still 7.6x faster (exponential BV branching)

### Hard (14 benchmarks)
```
Solved:     claude-smt=12/14, z3=12/14
Wins:       claude-smt=7, z3=3
Geo mean:   0.663x (claude 1.5x faster on commonly-solved instances)
```
**Key improvements:**
- bv16_mul_commutative: 2.6ms (was **TIMEOUT** — now solved via CSE)
- bv32_mul_commutative: 6.5ms (was **TIMEOUT** — now solved via CSE)
- pigeonhole_8: 459ms (was **TIMEOUT** — now solved via clause minimization)
- pigeonhole_9: 5.5s (was **TIMEOUT** — now solved via clause minimization)
- random3sat_150_639: 4.0ms (was 27.5ms — clause minimization helped)

**Remaining weaknesses:**
- bv32_nested_ite_10: 2.72s vs z3's 26ms (104x slower — needs lazy bit-blasting)
- bv16_compare_chain_200: 312ms vs z3's 110ms (2.8x slower)
- random3sat_200_852: 302ms vs z3's 134ms (2.2x slower)

### Overall
```
                    Before fixes    After fixes     z3
Solved:             45/53           50/53           50/53
Timeouts:           5               3               3
Correctness bugs:   2               0               0
Wins (vs z3):       39              43              5
Geo mean ratio:     0.337x          0.241x          ---
```

## What Was Fixed

### 1. bvudiv/bvurem Correctness Bug (Priority 1)
**Root cause**: `bvudiv(x,y)` and `bvurem(x,y)` created independent quotient/remainder
variables. When a formula referenced both operations on the same operands, the SAT
solver could assign inconsistent q,r pairs, violating the Euclidean property.

**Fix**: Added `bvdivrem()` that computes both q and r with shared constraints,
plus a `divrem_cache` in the solver so that multiple references to div/rem on the
same operands share the same variables.

**Impact**: bv8_div_property now correctly returns `unsat`. bv16/bv32 still timeout
(division verification requires multiplication in constraints — inherently expensive).

### 2. Term Canonicalization + CSE (Priority 2)
**Root cause**: `(bvmul x y)` and `(bvmul y x)` generated completely separate SAT
circuits. No shared structure was detected.

**Fix**: Added `canonicalize_bv_term()` that sorts operands of commutative BV ops
(bvadd, bvmul, bvand, bvor, bvxor), plus a `bv_term_cache` that maps canonical
terms to their BitVec encoding.

**Impact**: Multiplier commutativity now solved in <10ms for ALL bit-widths:
| Bits | Before | After  | Speedup |
|------|--------|--------|---------|
| 4    | 3.3ms  | 1.6ms  | 2x      |
| 8    | 4,830ms| 1.8ms  | 2,683x  |
| 16   | TIMEOUT| 2.6ms  | ∞       |
| 32   | TIMEOUT| 6.5ms  | ∞       |

### 3. Learned Clause Minimization (Priority 3)
**Root cause**: The CDCL `analyze()` function built learned clauses but did not
minimize them. Redundant literals accumulated, degrading unit propagation efficiency.

**Fix**: Added MiniSat-style self-subsumption minimization — after building a learned
clause, remove literals whose reason clauses are fully subsumed by literals already
in the clause (at level 0 or marked as seen).

**Impact**: Pigeonhole benchmarks dramatically improved:
| Problem       | Before  | After   | z3      |
|---------------|---------|---------|---------|
| pigeonhole_7  | 105ms   | 47ms    | 99ms    |
| pigeonhole_8  | TIMEOUT | 459ms   | 455ms   |
| pigeonhole_9  | TIMEOUT | 5.4s    | 4.7s    |

Random 3-SAT also improved (random3sat_150_639: 27.5ms → 4.0ms).

## Remaining Weaknesses

1. **Nested ITE at scale**: bv32_nested_ite_10 is 104x slower than z3. Needs lazy
   bit-blasting or BV-level ITE optimization.
2. **Division verification**: bv16/bv32_div_property timeout for both solvers due
   to multiplication in the constraint encoding. Needs algebraic simplification
   or alternative division circuit encoding.
3. **Large random 3-SAT**: random3sat_200_852 is 2.2x slower than z3. Would benefit
   from more CDCL improvements (variable elimination, subsumption, etc.).
4. **No preprocessing**: Missing SATElite-style preprocessing (variable elimination,
   subsumption, self-subsumption) that would help on structured UNSAT instances.

## Comparison with SMT-COMP Context

At SMT-COMP, solvers are ranked by **instances solved within timeout** (1200s).
After fixes, claude-smt matches z3's solve count (50/53 = 50/53) on this benchmark
suite, though the problems are still relatively easy/medium by competition standards.
On SMT-COMP's full QF_BV suite (6,861 benchmarks including very hard instances),
claude-smt would still solve significantly fewer instances than z3 or Bitwuzla.

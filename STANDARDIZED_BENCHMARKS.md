# Standardized Benchmark Results: An Honest Evaluation

## Methodology

Previous benchmarks used 14 hand-crafted problems that favored claude-smt (startup
time dominated, toy scale). This evaluation uses **53 benchmarks from standardized
families** drawn from SMT-LIB and academic literature:

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

## Results

### Easy (17 benchmarks)
```
Solved:     claude-smt=17/17, z3=17/17
Wins:       claude-smt=17, z3=0
Geo mean:   0.175x (claude 5.7x faster)
```
All easy benchmarks complete in <16ms for claude-smt. This is dominated by startup
time advantage (~2ms vs ~11ms). Not meaningful for solver quality.

### Medium (22 benchmarks)
```
Solved:     claude-smt=20/22, z3=21/22
Wins:       claude-smt=17, z3=4
Geo mean:   0.398x (claude 2.5x faster on solved instances)
```
**Key findings at medium difficulty:**
- claude-smt **fails to solve** bv8_div_property and bv16_div_property correctly
  (returns SAT when answer is UNSAT) — this is a **correctness bug** in bvudiv/bvurem
- bv8_mul_commutative: claude-smt takes 4.83s vs z3's 10.9ms (444x slower)
- bv16_nested_ite_8: claude-smt 84ms vs z3's 11.5ms (7.3x slower)
- z3 times out on bv16_div_property (both solvers struggle with division)

### Hard (14 benchmarks)
```
Solved:     claude-smt=8/14, z3=12/14
Wins:       claude-smt=5, z3=3
Geo mean:   0.878x (roughly equal on commonly-solved instances)
```
**Key findings at hard difficulty:**
- bv16_mul_commutative: claude-smt **TIMEOUT**, z3 solves in 10.3ms
- bv32_mul_commutative: claude-smt **TIMEOUT**, z3 solves in 10.5ms
- bv32_nested_ite_10: claude-smt 1.47s vs z3's 16.9ms (87x slower)
- pigeonhole_8: claude-smt **TIMEOUT**, z3 solves in 454ms
- pigeonhole_9: claude-smt **TIMEOUT**, z3 solves in 4.67s
- random3sat_200_852: claude-smt 364ms vs z3's 115ms (3.2x slower)
- random3sat_300_1278: **both timeout** at 30s
- claude-smt wins on bv32_factor, queens_10, queens_12, counter circuits

### Overall
```
                    claude-smt      z3
Solved:             45/53           50/53
Timeouts:           5               3
Correctness bugs:   2               0
Wins:               39              7
Geo mean ratio:     0.337x
```

## Honest Assessment

### Where claude-smt genuinely wins
1. **Startup time**: ~2ms vs ~11ms. Dominates all easy benchmarks.
2. **Simple BV arithmetic** (add, bitwise): fast bit-blasting with low overhead.
3. **Queens / graph coloring**: efficient encoding for these constraint patterns.
4. **Factor finding** (bv32_factor_0xdeadbeef): 4.8ms vs 38.9ms — genuine 8x win.

### Where claude-smt is destroyed
1. **Multiplier commutativity**: z3 uses algebraic rewriting to prove x*y = y*x
   without bit-blasting. claude-smt naively bit-blasts and generates ~O(n²) gates,
   then tries to prove UNSAT on a massive SAT formula.
   - 4-bit: 3.3ms vs 9.9ms (we win due to small size)
   - 8-bit: 4,830ms vs 10.9ms (z3 is **444x faster**)
   - 16-bit: TIMEOUT vs 10.3ms
   - 32-bit: TIMEOUT vs 10.5ms
   This is the single most damning result. z3's time is **constant** because it
   rewrites algebraically. Ours is exponential in bit-width.

2. **Pigeonhole principle**: requires sophisticated proof search for UNSAT.
   - n=7: 105ms vs 99ms (tied)
   - n=8: TIMEOUT vs 454ms
   - n=9: TIMEOUT vs 4.67s
   Exponential blowup in our CDCL solver without symmetry breaking.

3. **Nested ITE (BV)**: exponential branching in bit-blasted formulas.
   - depth 6, 8-bit: 5.4ms vs 10.5ms (we win)
   - depth 8, 16-bit: 84ms vs 11.5ms (z3 is 7x faster)
   - depth 10, 32-bit: 1,470ms vs 16.9ms (z3 is **87x faster**)

4. **Division correctness**: claude-smt returns WRONG ANSWERS for bvudiv/bvurem
   properties. This is not a performance issue — it's a soundness bug.

### What the previous benchmarks hid
The original "5.3x faster" claim was based on 14 problems where:
- 11 completed in <10ms (startup-dominated)
- 0 tested multiplier verification at 16+ bits
- 0 tested division properties
- 0 tested pigeonhole beyond n=6
- 0 tested nested ITE at depth >6
- 0 included correctness checking

### How this compares to SMT-COMP
At SMT-COMP, solvers are ranked by **instances solved within timeout** (typically 1200s).
Bitwuzla (current QF_BV champion) solves ~99% of QF_BV benchmarks. z3 solves ~95%.
claude-smt would solve perhaps 50-70% — placing it dead last among serious entries.

## Detailed Results Table

```
EASY (17 benchmarks): claude-smt 17/17, z3 17/17, claude wins all (startup advantage)

MEDIUM (22 benchmarks):
  claude wins:  bv32_overflow, bv32_power_of_two, bv8_counter_10steps,
                bv8_counter_50steps, bv16_counter_20steps, bv8_compare_chain_10,
                bv16_compare_chain_50, bv8_factor_0x48, bv16_factor_0xa8c0,
                bv8_nested_ite_6, bv8_div_property*, bv4_mul_commutative,
                pigeonhole_6, random3sat_50_213, random3sat_100_426,
                queens_8, petersen_3color
  z3 wins:      bv16_nested_ite_8 (7.3x), bv8_mul_commutative (444x),
                pigeonhole_7 (1.07x), random3sat_150_639 (1.17x)
  * = claude gives wrong answer (returns sat, correct is unsat)

HARD (14 benchmarks):
  claude wins:  bv32_div_property*, bv32_factor_0xdeadbeef (8x),
                bv16_counter_100steps, queens_10 (7x), queens_12 (6x)
  z3 wins:      bv16_mul_commutative, bv32_mul_commutative,
                bv32_nested_ite_10 (87x), bv16_compare_chain_200 (4.6x),
                pigeonhole_8, pigeonhole_9, random3sat_200_852 (3.2x)
  * = claude gives wrong answer
  Both timeout: random3sat_300_1278
```

## Conclusion

claude-smt has genuine strengths: fast startup, efficient simple BV arithmetic, and
good performance on certain constraint patterns (queens, factoring, graph coloring).

However, standardized benchmarks reveal critical weaknesses hidden by the original
hand-crafted benchmark suite:

1. **Correctness bugs** in division (bvudiv/bvurem) — the solver gives wrong answers
2. **Exponential blowup** on multiplier verification — z3 is 444x to infinitely faster
3. **Missing algebraic simplification** — z3's constant-time proofs vs our exponential bit-blasting
4. **Weak on large UNSAT proofs** — pigeonhole, large 3-SAT at phase transition

The "5.3x faster" headline from original benchmarks should be revised to:
**"Faster on small/simple instances due to startup advantage; dramatically slower
or incorrect on problems requiring sophisticated BV reasoning."**

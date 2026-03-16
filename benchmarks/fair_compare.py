#!/usr/bin/env python3
"""
Fair benchmark comparison: claude-smt vs z3

All solvers run via subprocess with the same SMT-LIB files to ensure
a fair comparison (same startup overhead, same I/O path).

Complex benchmarks are included to make startup time negligible.
"""

import os
import subprocess
import sys
import time
import math
from pathlib import Path

# --- Configuration ---
ITERATIONS = 10  # per benchmark per solver
WARMUP = 2
TIMEOUT = 60  # seconds per individual run

ROOT = Path(__file__).parent.parent
CLAUDE_SMT = ROOT / "target" / "release" / "claude-smt"
PROBLEMS_DIR = Path(__file__).parent / "problems"


def time_subprocess(cmd, iterations, warmup=WARMUP, timeout=TIMEOUT):
    """Time a subprocess command, return (median_ms, min_ms, error)."""
    # Warmup
    for _ in range(warmup):
        try:
            r = subprocess.run(cmd, capture_output=True, timeout=timeout)
            if r.returncode != 0:
                return None, None, r.stderr.decode()[:200]
        except subprocess.TimeoutExpired:
            return None, None, "TIMEOUT"

    times = []
    for _ in range(iterations):
        start = time.perf_counter()
        try:
            result = subprocess.run(cmd, capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, None, "TIMEOUT"
        elapsed = (time.perf_counter() - start) * 1000  # ms
        if result.returncode != 0:
            return None, None, result.stderr.decode()[:200]
        times.append(elapsed)

    times.sort()
    median = times[len(times) // 2]
    minimum = times[0]
    return median, minimum, None


def run_benchmarks():
    print("=" * 90)
    print("  Fair SMT Solver Comparison (all via subprocess + SMT-LIB files)")
    print("=" * 90)
    print(f"  Iterations: {ITERATIONS} (+ {WARMUP} warmup), Timeout: {TIMEOUT}s")
    print()

    # Check solver availability
    has_z3 = subprocess.run(["z3", "--version"], capture_output=True).returncode == 0
    has_claude = CLAUDE_SMT.exists()

    if has_z3:
        z3_ver = subprocess.run(["z3", "--version"], capture_output=True).stdout.decode().strip()
    else:
        z3_ver = "NOT FOUND"

    print(f"  claude-smt: {'OK' if has_claude else 'NOT FOUND'} ({CLAUDE_SMT})")
    print(f"  z3:         {z3_ver}")
    print()

    if not has_claude:
        print("ERROR: Build claude-smt first: cargo build --release")
        sys.exit(1)

    # Ordered list of benchmarks with expected results and complexity notes
    benchmark_order = [
        # Simple (startup-dominated)
        ("bool_formula", "sat"),
        ("bv8_equation", "sat"),
        ("bv8_compare", "sat"),
        ("int_simple", "sat"),
        ("int_3var", "sat"),
        # Medium
        ("bv16_mul", "sat"),
        ("bv16_multi_constraint", "sat"),
        ("bv32_add", "sat"),
        ("bv8_puzzle", "sat"),
        # Complex (startup negligible)
        ("bool_random3sat_150", None),  # may be sat or unsat
        ("bool_random3sat_250", None),
        ("bool_pigeonhole5", "unsat"),
        ("bool_pigeonhole6", "unsat"),
        ("bool_chain2000", "unsat"),
        ("bv32_mul_complex", "sat"),
    ]

    header = f"{'Benchmark':<35} {'Expected':>7} {'claude-smt':>14} {'z3':>14} {'ratio':>10} {'winner':>8}"
    print(header)
    print("-" * len(header))

    results = []
    for name, expected in benchmark_order:
        path = PROBLEMS_DIR / f"{name}.smt2"
        if not path.exists():
            print(f"{name:<35} {'???':>7} {'MISSING':>14} {'---':>14} {'---':>10} {'---':>8}")
            continue

        row = {"name": name, "expected": expected}

        # claude-smt
        t_claude, t_claude_min, err = time_subprocess(
            [str(CLAUDE_SMT), str(path)], ITERATIONS
        )
        if err:
            row["claude"] = None
            row["claude_err"] = err[:30]
        else:
            row["claude"] = t_claude
            row["claude_min"] = t_claude_min

        # z3 (also via subprocess, fair comparison)
        if has_z3:
            t_z3, t_z3_min, err = time_subprocess(
                ["z3", str(path)], ITERATIONS
            )
            if err:
                row["z3"] = None
                row["z3_err"] = err[:30]
            else:
                row["z3"] = t_z3
                row["z3_min"] = t_z3_min
        else:
            row["z3"] = None

        # Format output
        def fmt(v, err_key, row):
            if v is not None:
                return f"{v:.2f} ms"
            return row.get(err_key, "N/A")[:14]

        def ratio_str(ours, theirs):
            if ours is not None and theirs is not None and theirs > 0:
                r = ours / theirs
                return f"{r:.2f}x"
            return "---"

        def winner_str(ours, theirs):
            if ours is not None and theirs is not None:
                if ours < theirs * 0.95:
                    return "CLAUDE"
                elif theirs < ours * 0.95:
                    return "z3"
                else:
                    return "~tie"
            return "---"

        c_str = fmt(row["claude"], "claude_err", row)
        z_str = fmt(row["z3"], "z3_err", row)
        r_str = ratio_str(row["claude"], row["z3"])
        w_str = winner_str(row["claude"], row["z3"])

        exp_str = expected or "?"
        print(f"{name:<35} {exp_str:>7} {c_str:>14} {z_str:>14} {r_str:>10} {w_str:>8}")
        results.append(row)

    # Summary
    print()
    print("=" * 90)
    print("  Ratio: claude-smt / z3 (<1.0 means claude-smt is faster)")
    print()

    z3_ratios = []
    z3_ratios_complex = []  # only benchmarks where both took >5ms
    for r in results:
        if r.get("claude") and r.get("z3") and r["z3"] > 0:
            ratio = r["claude"] / r["z3"]
            z3_ratios.append(ratio)
            # "Complex" = both took more than 5ms (startup not dominant)
            if r["claude"] > 5 or r["z3"] > 5:
                z3_ratios_complex.append(ratio)

    if z3_ratios:
        geo = math.exp(sum(math.log(r) for r in z3_ratios) / len(z3_ratios))
        print(f"  Geometric mean (all):     {geo:.3f}x  ({len(z3_ratios)} benchmarks)")
    if z3_ratios_complex:
        geo_c = math.exp(sum(math.log(r) for r in z3_ratios_complex) / len(z3_ratios_complex))
        print(f"  Geometric mean (complex): {geo_c:.3f}x  ({len(z3_ratios_complex)} benchmarks, solve > 5ms)")

    # Count wins
    claude_wins = sum(1 for r in results if r.get("claude") and r.get("z3") and r["claude"] < r["z3"] * 0.95)
    z3_wins = sum(1 for r in results if r.get("claude") and r.get("z3") and r["z3"] < r["claude"] * 0.95)
    ties = sum(1 for r in results if r.get("claude") and r.get("z3")) - claude_wins - z3_wins
    print(f"\n  Wins: claude-smt={claude_wins}, z3={z3_wins}, ties={ties}")
    print()

    return results


if __name__ == "__main__":
    run_benchmarks()

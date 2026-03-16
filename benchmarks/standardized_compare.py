#!/usr/bin/env python3
"""
Standardized benchmark comparison: claude-smt vs z3

Uses benchmark families from SMT-LIB / academic literature — NOT hand-crafted
to favor any solver. Follows SMT-COMP methodology:
  - Both solvers via subprocess (same startup overhead)
  - Wall-clock timeout per instance
  - Report: solved instances, total time, geometric mean ratio
  - Separate results by difficulty tier (easy/medium/hard)

Benchmark sources documented in generate_standardized.py.
"""

import os
import subprocess
import sys
import time
import math
from pathlib import Path
from collections import defaultdict

# --- Configuration ---
ITERATIONS = 5
WARMUP = 2
TIMEOUT = 30  # seconds per run (SMT-COMP uses 1200s; we use 30s for practicality)

ROOT = Path(__file__).parent.parent
CLAUDE_SMT = ROOT / "target" / "release" / "claude-smt"
STANDARDIZED_DIR = Path(__file__).parent / "standardized"


def get_expected(smt2_path):
    """Extract expected result from file header."""
    with open(smt2_path) as f:
        for line in f:
            if line.startswith("; Expected:"):
                return line.split(":")[1].strip()
    return "unknown"


def get_difficulty(smt2_path):
    """Classify difficulty from path structure."""
    name = smt2_path.stem
    # Read from benchmark list
    return None  # will be set from manifest


def time_solver(cmd, iterations, warmup=WARMUP, timeout=TIMEOUT):
    """Time a solver, return (median_ms, output, error_or_None)."""
    output = None
    # Warmup
    for _ in range(warmup):
        try:
            r = subprocess.run(cmd, capture_output=True, timeout=timeout, text=True)
            output = r.stdout.strip().split('\n')[0].strip() if r.stdout else ""
        except subprocess.TimeoutExpired:
            return None, "TIMEOUT", "TIMEOUT"

    times = []
    for _ in range(iterations):
        start = time.perf_counter()
        try:
            result = subprocess.run(cmd, capture_output=True, timeout=timeout, text=True)
        except subprocess.TimeoutExpired:
            return None, "TIMEOUT", "TIMEOUT"
        elapsed = (time.perf_counter() - start) * 1000
        out = result.stdout.strip().split('\n')[0].strip() if result.stdout else ""
        if result.returncode != 0:
            return None, out, result.stderr[:200]
        output = out
        times.append(elapsed)

    times.sort()
    median = times[len(times) // 2]
    return median, output, None


# Benchmark manifest: (subdir, name, expected, difficulty)
BENCHMARKS = [
    # --- QF_BV Easy ---
    ("qf_bv", "bv8_ripple_carry", "sat", "easy"),
    ("qf_bv", "bv16_ripple_carry", "sat", "easy"),
    ("qf_bv", "bv32_ripple_carry", "sat", "easy"),
    ("qf_bv", "bv32_demorgan", "unsat", "easy"),
    ("qf_bv", "bv64_demorgan", "unsat", "easy"),
    ("qf_bv", "bv32_distributivity", "unsat", "easy"),
    ("qf_bv", "bv16_sign_ext_trunc", "unsat", "easy"),
    ("qf_bv", "bv32_sign_ext_trunc", "unsat", "easy"),
    ("qf_bv", "bv16_shift_props", "sat", "easy"),
    ("qf_bv", "bv32_shift_props", "sat", "easy"),
    ("qf_bv", "bv8_power_of_two", "sat", "easy"),
    ("qf_bv", "bv16_power_of_two", "sat", "easy"),
    ("qf_bv", "bv8_overflow", "sat", "easy"),
    ("qf_bv", "bv16_overflow", "sat", "easy"),
    # --- QF_BV Medium ---
    ("qf_bv", "bv32_overflow", "sat", "medium"),
    ("qf_bv", "bv32_power_of_two", "sat", "medium"),
    ("qf_bv", "bv8_counter_10steps", "sat", "medium"),
    ("qf_bv", "bv8_counter_50steps", "sat", "medium"),
    ("qf_bv", "bv16_counter_20steps", "sat", "medium"),
    ("qf_bv", "bv8_compare_chain_10", "sat", "medium"),
    ("qf_bv", "bv16_compare_chain_50", "sat", "medium"),
    ("qf_bv", "bv8_factor_0x48", "sat", "medium"),
    ("qf_bv", "bv16_factor_0xa8c0", "sat", "medium"),
    ("qf_bv", "bv8_nested_ite_6", "sat", "medium"),
    ("qf_bv", "bv16_nested_ite_8", "sat", "medium"),
    ("qf_bv", "bv8_div_property", "unsat", "medium"),
    ("qf_bv", "bv16_div_property", "unsat", "medium"),
    ("qf_bv", "bv4_mul_commutative", "unsat", "medium"),
    ("qf_bv", "bv8_mul_commutative", "unsat", "medium"),
    # --- QF_BV Hard ---
    ("qf_bv", "bv16_mul_commutative", "unsat", "hard"),
    ("qf_bv", "bv32_mul_commutative", "unsat", "hard"),
    ("qf_bv", "bv32_div_property", "unsat", "hard"),
    ("qf_bv", "bv32_factor_0xdeadbeef", "sat", "hard"),
    ("qf_bv", "bv16_counter_100steps", "sat", "hard"),
    ("qf_bv", "bv32_nested_ite_10", "sat", "hard"),
    ("qf_bv", "bv16_compare_chain_200", "sat", "hard"),
    # --- QF_UF Easy ---
    ("qf_uf", "bool_chain_500", "unsat", "easy"),
    ("qf_uf", "bool_chain_5000", "unsat", "easy"),
    ("qf_uf", "pigeonhole_4", "unsat", "easy"),
    # --- QF_UF Medium ---
    ("qf_uf", "pigeonhole_6", "unsat", "medium"),
    ("qf_uf", "pigeonhole_7", "unsat", "medium"),
    ("qf_uf", "random3sat_50_213", "unknown", "medium"),
    ("qf_uf", "random3sat_100_426", "unknown", "medium"),
    ("qf_uf", "random3sat_150_639", "unknown", "medium"),
    ("qf_uf", "queens_8", "sat", "medium"),
    ("qf_uf", "petersen_3color", "unknown", "medium"),
    # --- QF_UF Hard ---
    ("qf_uf", "pigeonhole_8", "unsat", "hard"),
    ("qf_uf", "pigeonhole_9", "unsat", "hard"),
    ("qf_uf", "random3sat_200_852", "unknown", "hard"),
    ("qf_uf", "random3sat_300_1278", "unknown", "hard"),
    ("qf_uf", "queens_10", "sat", "hard"),
    ("qf_uf", "queens_12", "sat", "hard"),
    ("qf_uf", "random_graph20_3color", "unknown", "hard"),
]


def run_benchmarks():
    print("=" * 100)
    print("  Standardized SMT Benchmark Comparison")
    print("  Benchmark families: SMT-LIB / academic literature (NOT hand-crafted)")
    print("=" * 100)
    print(f"  Iterations: {ITERATIONS} (+ {WARMUP} warmup), Timeout: {TIMEOUT}s")
    print()

    # Check solver availability
    has_z3 = subprocess.run(["z3", "--version"], capture_output=True).returncode == 0
    has_claude = CLAUDE_SMT.exists()

    if has_z3:
        z3_ver = subprocess.run(["z3", "--version"], capture_output=True, text=True).stdout.strip()
    else:
        z3_ver = "NOT FOUND"

    print(f"  claude-smt: {'OK' if has_claude else 'NOT FOUND'}")
    print(f"  z3:         {z3_ver}")
    print()

    if not has_claude:
        print("ERROR: Build first: cargo build --release")
        sys.exit(1)

    results = []
    current_diff = None

    header = f"{'Benchmark':<40} {'Exp':>5} {'claude-smt':>12} {'z3':>12} {'ratio':>8} {'ok?':>5} {'winner':>8}"
    sep = "-" * len(header)

    for subdir, name, expected, difficulty in BENCHMARKS:
        if difficulty != current_diff:
            current_diff = difficulty
            print()
            print(f"  === {difficulty.upper()} ===")
            print(header)
            print(sep)

        path = STANDARDIZED_DIR / subdir / f"{name}.smt2"
        if not path.exists():
            print(f"{name:<40} MISSING")
            continue

        row = {"name": name, "subdir": subdir, "expected": expected, "difficulty": difficulty}

        # claude-smt
        t_c, out_c, err_c = time_solver([str(CLAUDE_SMT), str(path)], ITERATIONS)
        row["claude_time"] = t_c
        row["claude_out"] = out_c
        row["claude_err"] = err_c

        # z3
        if has_z3:
            t_z, out_z, err_z = time_solver(["z3", str(path)], ITERATIONS)
            row["z3_time"] = t_z
            row["z3_out"] = out_z
            row["z3_err"] = err_z
        else:
            row["z3_time"] = None

        # Correctness check
        def check_correct(output, expected):
            if expected == "unknown":
                return output in ("sat", "unsat")
            return output == expected

        c_correct = check_correct(out_c, expected) if err_c is None else False
        z_correct = check_correct(row.get("z3_out", ""), expected) if row.get("z3_err") is None else False
        row["claude_correct"] = c_correct
        row["z3_correct"] = z_correct

        # Format
        def fmt_time(t, err):
            if err == "TIMEOUT":
                return "TIMEOUT"
            if t is not None:
                if t >= 1000:
                    return f"{t/1000:.2f}s"
                return f"{t:.1f}ms"
            return "ERR"

        c_str = fmt_time(t_c, err_c)
        z_str = fmt_time(row.get("z3_time"), row.get("z3_err"))

        if t_c and row.get("z3_time"):
            ratio = t_c / row["z3_time"]
            r_str = f"{ratio:.2f}x"
            if t_c < row["z3_time"] * 0.95:
                w_str = "CLAUDE"
            elif row["z3_time"] < t_c * 0.95:
                w_str = "z3"
            else:
                w_str = "~tie"
        elif t_c and not row.get("z3_time"):
            r_str = "---"
            w_str = "CLAUDE" if row.get("z3_err") == "TIMEOUT" else "---"
        elif not t_c and row.get("z3_time"):
            r_str = "---"
            w_str = "z3"
        else:
            r_str = "---"
            w_str = "---"

        ok_str = ""
        if c_correct and z_correct:
            ok_str = "ok"
        elif not c_correct and not z_correct:
            ok_str = "BOTH?"
        elif not c_correct:
            ok_str = "C-ERR"
        elif not z_correct:
            ok_str = "Z-ERR"

        exp_str = expected if expected != "unknown" else "?"
        display_name = f"{subdir}/{name}"
        print(f"{display_name:<40} {exp_str:>5} {c_str:>12} {z_str:>12} {r_str:>8} {ok_str:>5} {w_str:>8}")
        results.append(row)

    # === SUMMARY ===
    print()
    print("=" * 100)
    print("  SUMMARY (SMT-COMP style)")
    print("=" * 100)

    # Per-difficulty stats
    for diff in ["easy", "medium", "hard"]:
        diff_results = [r for r in results if r["difficulty"] == diff]
        if not diff_results:
            continue

        c_solved = sum(1 for r in diff_results if r["claude_correct"])
        z_solved = sum(1 for r in diff_results if r.get("z3_correct", False))
        total = len(diff_results)

        c_wins = sum(1 for r in diff_results
                     if r.get("claude_time") and r.get("z3_time")
                     and r["claude_time"] < r["z3_time"] * 0.95)
        z_wins = sum(1 for r in diff_results
                     if r.get("claude_time") and r.get("z3_time")
                     and r["z3_time"] < r["claude_time"] * 0.95)

        ratios = [r["claude_time"] / r["z3_time"]
                  for r in diff_results
                  if r.get("claude_time") and r.get("z3_time") and r["z3_time"] > 0]
        geo = math.exp(sum(math.log(x) for x in ratios) / len(ratios)) if ratios else float('nan')

        # Total solve time
        c_total_ms = sum(r["claude_time"] for r in diff_results if r.get("claude_time"))
        z_total_ms = sum(r.get("z3_time", 0) or 0 for r in diff_results)

        print(f"\n  {diff.upper()} ({total} benchmarks):")
        print(f"    Solved:         claude-smt={c_solved}/{total}, z3={z_solved}/{total}")
        print(f"    Wins:           claude-smt={c_wins}, z3={z_wins}")
        if not math.isnan(geo):
            print(f"    Geo mean ratio: {geo:.3f}x (claude/z3, <1 = claude faster)")
        print(f"    Total time:     claude-smt={c_total_ms:.0f}ms, z3={z_total_ms:.0f}ms")

    # Overall
    c_total_solved = sum(1 for r in results if r["claude_correct"])
    z_total_solved = sum(1 for r in results if r.get("z3_correct", False))
    total = len(results)
    all_ratios = [r["claude_time"] / r["z3_time"]
                  for r in results
                  if r.get("claude_time") and r.get("z3_time") and r["z3_time"] > 0]
    all_geo = math.exp(sum(math.log(x) for x in all_ratios) / len(all_ratios)) if all_ratios else float('nan')

    c_total_wins = sum(1 for r in results
                       if r.get("claude_time") and r.get("z3_time")
                       and r["claude_time"] < r["z3_time"] * 0.95)
    z_total_wins = sum(1 for r in results
                       if r.get("claude_time") and r.get("z3_time")
                       and r["z3_time"] < r["claude_time"] * 0.95)

    c_timeouts = sum(1 for r in results if r.get("claude_err") == "TIMEOUT")
    z_timeouts = sum(1 for r in results if r.get("z3_err") == "TIMEOUT")

    print(f"\n  OVERALL ({total} benchmarks):")
    print(f"    Solved:         claude-smt={c_total_solved}/{total}, z3={z_total_solved}/{total}")
    print(f"    Timeouts:       claude-smt={c_timeouts}, z3={z_timeouts}")
    print(f"    Wins:           claude-smt={c_total_wins}, z3={z_total_wins}")
    if not math.isnan(all_geo):
        print(f"    Geo mean ratio: {all_geo:.3f}x (claude/z3, <1 = claude faster)")
    print()

    # Per-theory breakdown
    for theory in ["qf_bv", "qf_uf"]:
        theory_results = [r for r in results if r["subdir"] == theory]
        if not theory_results:
            continue
        c_s = sum(1 for r in theory_results if r["claude_correct"])
        z_s = sum(1 for r in theory_results if r.get("z3_correct", False))
        t = len(theory_results)
        ratios = [r["claude_time"] / r["z3_time"]
                  for r in theory_results
                  if r.get("claude_time") and r.get("z3_time") and r["z3_time"] > 0]
        geo = math.exp(sum(math.log(x) for x in ratios) / len(ratios)) if ratios else float('nan')
        geo_str = f"{geo:.3f}x" if not math.isnan(geo) else "N/A"
        print(f"  {theory.upper():>8}: solved {c_s}/{t} (claude) vs {z_s}/{t} (z3), geo mean ratio: {geo_str}")

    print()
    return results


if __name__ == "__main__":
    run_benchmarks()

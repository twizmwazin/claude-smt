#!/usr/bin/env python3
"""
Benchmark comparison: claude-smt vs z3 vs cvc5

Runs identical SMT-LIB problems on all three solvers and reports timing.
Uses subprocess for claude-smt and z3, Python API for cvc5.
"""

import os
import subprocess
import sys
import time
from pathlib import Path

# --- Configuration ---
ITERATIONS = 50  # per benchmark per solver
WARMUP = 5
TIMEOUT = 30  # seconds per individual run

ROOT = Path(__file__).parent.parent
CLAUDE_SMT = ROOT / "target" / "release" / "claude-smt"
PROBLEMS_DIR = Path(__file__).parent / "problems"


def time_command(cmd, iterations, warmup=WARMUP):
    """Time a shell command over multiple iterations, return median ms."""
    # Warmup
    for _ in range(warmup):
        try:
            subprocess.run(cmd, capture_output=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return None, "TIMEOUT"

    times = []
    for _ in range(iterations):
        start = time.perf_counter()
        try:
            result = subprocess.run(cmd, capture_output=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return None, "TIMEOUT"
        elapsed = (time.perf_counter() - start) * 1000  # ms
        if result.returncode != 0:
            return None, result.stderr.decode()[:200]
        times.append(elapsed)

    times.sort()
    median = times[len(times) // 2]
    return median, None


def time_cvc5_api(problem_path, iterations, warmup=WARMUP):
    """Time cvc5 via Python API using parseSMTLIB2."""
    try:
        from cvc5 import Solver, InputParser, SymbolManager, InputLanguage
    except ImportError:
        return None, "cvc5 not installed"

    content = problem_path.read_text()

    def run_cvc5_once():
        s = Solver()
        sm = SymbolManager(s)
        parser = InputParser(s, sm)
        parser.setStringInput(InputLanguage.SMT_LIB_2_6, content, "bench")
        while True:
            cmd = parser.nextCommand()
            if cmd.isNull():
                break
            cmd.invoke(s, sm)

    # Warmup
    for _ in range(warmup):
        try:
            run_cvc5_once()
        except Exception:
            return time_command_cvc5_subprocess(problem_path, iterations, warmup)

    times = []
    for _ in range(iterations):
        start = time.perf_counter()
        try:
            run_cvc5_once()
        except Exception as e:
            return None, str(e)[:200]
        elapsed = (time.perf_counter() - start) * 1000
        times.append(elapsed)

    times.sort()
    median = times[len(times) // 2]
    return median, None


def time_command_cvc5_subprocess(problem_path, iterations, warmup=WARMUP):
    """Fallback: time cvc5 via a subprocess Python wrapper."""
    script = f'''
import sys
from cvc5 import Solver, InputParser, SymbolManager
content = open("{problem_path}").read()
s = Solver()
s.setOption("produce-models", "false")
sm = SymbolManager(s)
parser = InputParser(s, sm)
parser.setStringInput(0, content, "bench")
while True:
    cmd = parser.nextCommand()
    if cmd.isNull():
        break
    cmd.invoke(s, sm)
'''
    cmd = [sys.executable, "-c", script]
    return time_command(cmd, iterations, warmup)


def generate_pigeonhole_smt2(n):
    """Generate pigeonhole principle: n pigeons into n-1 holes (UNSAT)."""
    holes = n - 1
    lines = ["(set-logic QF_UF)"]
    for i in range(n):
        for j in range(holes):
            lines.append(f"(declare-const p{i}_{j} Bool)")
    # Each pigeon in some hole
    for i in range(n):
        clause = " ".join(f"p{i}_{j}" for j in range(holes))
        lines.append(f"(assert (or {clause}))")
    # No two pigeons in same hole
    for j in range(holes):
        for i1 in range(n):
            for i2 in range(i1 + 1, n):
                lines.append(f"(assert (not (and p{i1}_{j} p{i2}_{j})))")
    lines.append("(check-sat)")
    lines.append("(exit)")
    return "\n".join(lines)


def generate_chain_smt2(n):
    """Generate implication chain: x1 => x2 => ... => xn, x1=T, xn=F (UNSAT)."""
    lines = ["(set-logic QF_UF)"]
    for i in range(1, n + 1):
        lines.append(f"(declare-const x{i} Bool)")
    lines.append("(assert x1)")
    for i in range(1, n):
        lines.append(f"(assert (or (not x{i}) x{i+1}))")
    lines.append(f"(assert (not x{n}))")
    lines.append("(check-sat)")
    lines.append("(exit)")
    return "\n".join(lines)


def run_benchmarks():
    print("=" * 78)
    print("  SMT Solver Comparison: claude-smt vs z3 vs cvc5")
    print("=" * 78)
    print(f"  Iterations per benchmark: {ITERATIONS} (+ {WARMUP} warmup)")
    print()

    # Check solver availability
    has_z3 = subprocess.run(["z3", "--version"], capture_output=True).returncode == 0
    has_cvc5 = False
    try:
        from cvc5 import Solver, InputParser, SymbolManager, InputLanguage
        has_cvc5 = True
    except ImportError:
        pass
    has_claude = CLAUDE_SMT.exists()

    print(f"  claude-smt: {'OK' if has_claude else 'NOT FOUND'} ({CLAUDE_SMT})")
    print(f"  z3:         {'OK' if has_z3 else 'NOT FOUND'}")
    print(f"  cvc5:       {'OK (Python API)' if has_cvc5 else 'NOT FOUND'}")
    print()

    if not has_claude:
        print("ERROR: Build claude-smt first: cargo build --release")
        sys.exit(1)

    # Collect benchmarks: (name, smt2_path, iterations_override)
    benchmarks = []

    # File-based benchmarks
    for f in sorted(PROBLEMS_DIR.glob("*.smt2")):
        benchmarks.append((f.stem, f, ITERATIONS))

    # Generated benchmarks (written to temp files)
    import tempfile
    tmpdir = Path(tempfile.mkdtemp())

    for n in [4]:
        p = tmpdir / f"pigeonhole_{n}.smt2"
        p.write_text(generate_pigeonhole_smt2(n))
        benchmarks.append((f"pigeonhole({n}) UNSAT", p, ITERATIONS))

    for n in [100, 500]:
        p = tmpdir / f"chain_{n}.smt2"
        p.write_text(generate_chain_smt2(n))
        benchmarks.append((f"chain({n}) UNSAT", p, ITERATIONS))

    # Print results table
    header = f"{'Benchmark':<30} {'claude-smt':>12} {'z3':>12} {'cvc5':>12} {'vs z3':>10} {'vs cvc5':>10}"
    print(header)
    print("-" * len(header))

    results = []
    for name, path, iters in benchmarks:
        row = {"name": name}

        # claude-smt
        t_claude, err = time_command([str(CLAUDE_SMT), str(path)], iters)
        if err:
            row["claude"] = f"ERR"
        else:
            row["claude"] = t_claude

        # z3
        if has_z3:
            t_z3, err = time_command(["z3", str(path)], iters)
            if err:
                row["z3"] = "ERR"
            else:
                row["z3"] = t_z3
        else:
            row["z3"] = "N/A"

        # cvc5
        if has_cvc5:
            t_cvc5, err = time_cvc5_api(path, iters)
            if err:
                row["cvc5"] = "ERR"
            else:
                row["cvc5"] = t_cvc5
        else:
            row["cvc5"] = "N/A"

        # Format output
        def fmt(v):
            if isinstance(v, (int, float)):
                return f"{v:.3f} ms"
            return str(v)

        def ratio(ours, theirs):
            if isinstance(ours, (int, float)) and isinstance(theirs, (int, float)) and theirs > 0:
                r = ours / theirs
                return f"{r:.2f}x"
            return "---"

        c_str = fmt(row["claude"])
        z_str = fmt(row["z3"])
        v_str = fmt(row["cvc5"])
        rz = ratio(row["claude"], row["z3"])
        rv = ratio(row["claude"], row["cvc5"])

        print(f"{name:<30} {c_str:>12} {z_str:>12} {v_str:>12} {rz:>10} {rv:>10}")
        results.append(row)

    # Summary
    print()
    print("=" * 78)
    print("  Ratio interpretation: <1.0x means claude-smt is FASTER")
    print("                        >1.0x means claude-smt is SLOWER")
    print()

    # Compute geometric mean of ratios
    import math
    z3_ratios = []
    cvc5_ratios = []
    for r in results:
        if isinstance(r["claude"], (int, float)) and isinstance(r["z3"], (int, float)) and r["z3"] > 0:
            z3_ratios.append(r["claude"] / r["z3"])
        if isinstance(r["claude"], (int, float)) and isinstance(r["cvc5"], (int, float)) and r["cvc5"] > 0:
            cvc5_ratios.append(r["claude"] / r["cvc5"])

    if z3_ratios:
        geo_z3 = math.exp(sum(math.log(r) for r in z3_ratios) / len(z3_ratios))
        print(f"  Geometric mean vs z3:  {geo_z3:.2f}x  (across {len(z3_ratios)} benchmarks)")
    if cvc5_ratios:
        geo_cvc5 = math.exp(sum(math.log(r) for r in cvc5_ratios) / len(cvc5_ratios))
        print(f"  Geometric mean vs cvc5: {geo_cvc5:.2f}x  (across {len(cvc5_ratios)} benchmarks)")

    print()

    # Cleanup
    import shutil
    shutil.rmtree(tmpdir, ignore_errors=True)

    return results


if __name__ == "__main__":
    run_benchmarks()

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use claude_smt::bitvector::{BitBlaster, BitVec};
use claude_smt::sat::{Lit, SatResult, SatSolver};
use claude_smt::solver::SmtSolver;

// ============================================================
// SAT solver benchmarks
// ============================================================

/// Pigeonhole principle: n pigeons into n-1 holes (always UNSAT)
fn pigeonhole(n: usize) -> SatSolver {
    let holes = n - 1;
    let mut solver = SatSolver::new();

    // Create variables: p[i][j] = pigeon i in hole j
    // Variable numbering: pigeon i, hole j => i * holes + j + 1
    let var = |i: usize, j: usize| -> Lit { (i * holes + j + 1) as Lit };

    // Each pigeon must be in some hole
    for i in 0..n {
        let clause: Vec<Lit> = (0..holes).map(|j| var(i, j)).collect();
        solver.add_clause(clause);
    }

    // No two pigeons in the same hole
    for j in 0..holes {
        for i1 in 0..n {
            for i2 in (i1 + 1)..n {
                solver.add_clause(vec![-var(i1, j), -var(i2, j)]);
            }
        }
    }

    solver
}

fn bench_sat_pigeonhole(c: &mut Criterion) {
    let mut group = c.benchmark_group("sat_pigeonhole");
    group.sample_size(10);
    for n in [4, 5, 6] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter(|| {
                let mut solver = pigeonhole(n);
                assert_eq!(solver.solve(), SatResult::Unsat);
            });
        });
    }
    group.finish();
}

/// Random 3-SAT at the phase transition (ratio ~4.27)
fn random_3sat(num_vars: usize, num_clauses: usize, seed: u64) -> SatSolver {
    let mut solver = SatSolver::new();
    for _ in 0..num_vars {
        solver.new_var();
    }
    let mut rng = seed;
    for _ in 0..num_clauses {
        let mut clause = Vec::with_capacity(3);
        for _ in 0..3 {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
            let v = ((rng >> 33) as usize % num_vars) + 1;
            let sign = if (rng >> 32) & 1 == 0 { 1 } else { -1 };
            clause.push(sign * v as Lit);
        }
        solver.add_clause(clause);
    }
    solver
}

fn bench_sat_random3sat(c: &mut Criterion) {
    let mut group = c.benchmark_group("sat_random3sat");
    group.sample_size(10);
    for &(vars, clauses) in &[(20, 85), (50, 213), (100, 427)] {
        group.bench_with_input(
            BenchmarkId::new("v_c", format!("{}_{}", vars, clauses)),
            &(vars, clauses),
            |b, &(v, cl)| {
                b.iter(|| {
                    let mut solver = random_3sat(v, cl, 12345);
                    black_box(solver.solve());
                });
            },
        );
    }
    group.finish();
}

/// Long chain of implications: x1 => x2 => ... => xn, with x1=true, -xn
fn bench_sat_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("sat_implication_chain");
    for &n in &[100, 500, 1000] {
        group.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, &n| {
            b.iter(|| {
                let mut solver = SatSolver::new();
                for _ in 0..n {
                    solver.new_var();
                }
                solver.add_clause(vec![1]); // x1 = true
                for i in 1..n {
                    // xi => xi+1: (-xi OR xi+1)
                    solver.add_clause(vec![-(i as Lit), (i + 1) as Lit]);
                }
                solver.add_clause(vec![-(n as Lit)]); // -xn
                assert_eq!(solver.solve(), SatResult::Unsat);
            });
        });
    }
    group.finish();
}

// ============================================================
// Bitvector benchmarks
// ============================================================

fn bench_bv_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("bv_add");
    for &width in &[8, 16, 32, 64] {
        group.bench_with_input(BenchmarkId::from_parameter(width), &width, |b, &w| {
            b.iter(|| {
                let mut solver = SatSolver::new();
                let a = BitVec::new_variable(&mut solver, w);
                let b_bv = BitVec::new_variable(&mut solver, w);
                let result = BitVec::from_constant(&mut solver, 42, w);
                let mut bb = BitBlaster::new(&mut solver);
                let sum = bb.bvadd(&a, &b_bv);
                bb.assert_eq(&sum, &result);
                black_box(solver.solve());
            });
        });
    }
    group.finish();
}

fn bench_bv_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("bv_mul");
    group.sample_size(10);
    for &width in &[4, 8, 12] {
        group.bench_with_input(BenchmarkId::from_parameter(width), &width, |b, &w| {
            b.iter(|| {
                let mut solver = SatSolver::new();
                let a = BitVec::new_variable(&mut solver, w);
                let b_bv = BitVec::from_constant(&mut solver, 7, w);
                let result = BitVec::from_constant(&mut solver, 21, w);
                let mut bb = BitBlaster::new(&mut solver);
                let product = bb.bvmul(&a, &b_bv);
                bb.assert_eq(&product, &result);
                black_box(solver.solve());
            });
        });
    }
    group.finish();
}

fn bench_bv_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("bv_comparison");
    for &width in &[8, 16, 32] {
        group.bench_with_input(BenchmarkId::from_parameter(width), &width, |b, &w| {
            b.iter(|| {
                let mut solver = SatSolver::new();
                let a = BitVec::new_variable(&mut solver, w);
                let bound = BitVec::from_constant(&mut solver, 100, w);
                let mut bb = BitBlaster::new(&mut solver);
                let lt = bb.bvult_lit(&a, &bound);
                solver.add_clause(vec![lt]);
                black_box(solver.solve());
            });
        });
    }
    group.finish();
}

// ============================================================
// Theory solver benchmarks
// ============================================================

fn bench_theory_int_arithmetic(c: &mut Criterion) {
    c.bench_function("theory_int_simple", |b| {
        b.iter(|| {
            let mut smt = SmtSolver::new();
            let result = smt.process_input(
                "(declare-const x Int)
                 (declare-const y Int)
                 (assert (= (+ x y) 10))
                 (assert (= (- x y) 4))
                 (check-sat)",
            );
            black_box(result);
        });
    });
}

fn bench_theory_int_multi_var(c: &mut Criterion) {
    c.bench_function("theory_int_3var", |b| {
        b.iter(|| {
            let mut smt = SmtSolver::new();
            let result = smt.process_input(
                "(declare-const x Int)
                 (declare-const y Int)
                 (declare-const z Int)
                 (assert (= (+ x y) 10))
                 (assert (= (+ y z) 15))
                 (assert (> x 0))
                 (assert (> z 0))
                 (check-sat)",
            );
            black_box(result);
        });
    });
}

fn bench_theory_string(c: &mut Criterion) {
    c.bench_function("theory_string", |b| {
        b.iter(|| {
            let mut smt = SmtSolver::new();
            let result = smt.process_input(
                "(declare-const s String)
                 (assert (= s \"hello\"))
                 (assert (= (str.len s) 5))
                 (check-sat)",
            );
            black_box(result);
        });
    });
}

// ============================================================
// End-to-end SMT-LIB benchmarks
// ============================================================

fn bench_smtlib_bool(c: &mut Criterion) {
    c.bench_function("smtlib_bool_formula", |b| {
        b.iter(|| {
            let mut smt = SmtSolver::new();
            let result = smt.process_input(
                "(declare-const p Bool)
                 (declare-const q Bool)
                 (declare-const r Bool)
                 (assert (or (and p q) (and (not p) r)))
                 (assert (not (and q r)))
                 (assert (or p q))
                 (check-sat)",
            );
            black_box(result);
        });
    });
}

fn bench_smtlib_bv8_equation(c: &mut Criterion) {
    c.bench_function("smtlib_bv8_equation", |b| {
        b.iter(|| {
            let mut smt = SmtSolver::new();
            let result = smt.process_input(
                "(set-logic QF_BV)
                 (declare-const x (_ BitVec 8))
                 (declare-const y (_ BitVec 8))
                 (assert (= (bvadd x y) #x1A))
                 (assert (= (bvsub x y) #x04))
                 (check-sat)",
            );
            black_box(result);
        });
    });
}

fn bench_smtlib_bv16_mul(c: &mut Criterion) {
    c.bench_function("smtlib_bv16_mul", |b| {
        b.iter(|| {
            let mut smt = SmtSolver::new();
            let result = smt.process_input(
                "(set-logic QF_BV)
                 (declare-const x (_ BitVec 16))
                 (assert (= (bvmul x #x0007) #x0015))
                 (check-sat)",
            );
            black_box(result);
        });
    });
}

fn bench_parsing(c: &mut Criterion) {
    c.bench_function("parsing_large_input", |b| {
        // Generate a large input with many assertions
        let mut input = String::new();
        input.push_str("(set-logic QF_LIA)\n");
        for i in 0..50 {
            input.push_str(&format!("(declare-const x{} Int)\n", i));
        }
        for i in 0..49 {
            input.push_str(&format!("(assert (> x{} x{}))\n", i, i + 1));
        }
        input.push_str("(assert (> x0 100))\n");
        input.push_str("(assert (> x49 0))\n");

        b.iter(|| {
            let mut smt = SmtSolver::new();
            let result = smt.process_input(&input);
            black_box(result);
        });
    });
}

criterion_group!(
    benches,
    bench_sat_pigeonhole,
    bench_sat_random3sat,
    bench_sat_chain,
    bench_bv_add,
    bench_bv_mul,
    bench_bv_comparison,
    bench_theory_int_arithmetic,
    bench_theory_int_multi_var,
    bench_theory_string,
    bench_smtlib_bool,
    bench_smtlib_bv8_equation,
    bench_smtlib_bv16_mul,
    bench_parsing,
);
criterion_main!(benches);

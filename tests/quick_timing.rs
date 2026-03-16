use std::time::Instant;

use claude_smt::bitvector::{BitBlaster, BitVec};
use claude_smt::sat::{Lit, SatResult, SatSolver};
use claude_smt::solver::SmtSolver;

fn pigeonhole(n: usize) -> SatSolver {
    let holes = n - 1;
    let mut solver = SatSolver::new();
    let var = |i: usize, j: usize| -> Lit { (i * holes + j + 1) as Lit };
    for i in 0..n {
        let clause: Vec<Lit> = (0..holes).map(|j| var(i, j)).collect();
        solver.add_clause(clause);
    }
    for j in 0..holes {
        for i1 in 0..n {
            for i2 in (i1 + 1)..n {
                solver.add_clause(vec![-var(i1, j), -var(i2, j)]);
            }
        }
    }
    solver
}

fn bench_n<F: Fn()>(name: &str, n: u32, f: F) {
    let start = Instant::now();
    for _ in 0..n {
        f();
    }
    let elapsed = start.elapsed();
    let per_iter = elapsed.as_secs_f64() * 1000.0 / n as f64;
    println!("{:45} {:>10.3} ms/iter  ({} iters, {:.2}s total)", name, per_iter, n, elapsed.as_secs_f64());
}

#[test]
fn quick_benchmarks() {
    println!("\n===== SOLVER TIMING BENCHMARKS =====\n");

    bench_n("SAT: pigeonhole(4) UNSAT", 200, || {
        let mut s = pigeonhole(4);
        assert_eq!(s.solve(), SatResult::Unsat);
    });

    bench_n("SAT: chain(500) UNSAT", 200, || {
        let mut solver = SatSolver::new();
        let n = 500usize;
        for _ in 0..n { solver.new_var(); }
        solver.add_clause(vec![1]);
        for i in 1..n { solver.add_clause(vec![-(i as Lit), (i + 1) as Lit]); }
        solver.add_clause(vec![-(n as Lit)]);
        assert_eq!(solver.solve(), SatResult::Unsat);
    });

    bench_n("SAT: chain(1000) UNSAT", 100, || {
        let mut solver = SatSolver::new();
        let n = 1000usize;
        for _ in 0..n { solver.new_var(); }
        solver.add_clause(vec![1]);
        for i in 1..n { solver.add_clause(vec![-(i as Lit), (i + 1) as Lit]); }
        solver.add_clause(vec![-(n as Lit)]);
        assert_eq!(solver.solve(), SatResult::Unsat);
    });

    bench_n("BV: 8-bit add SAT", 200, || {
        let mut solver = SatSolver::new();
        let a = BitVec::new_variable(&mut solver, 8);
        let b = BitVec::new_variable(&mut solver, 8);
        let r = BitVec::from_constant(&mut solver, 42, 8);
        let mut bb = BitBlaster::new(&mut solver);
        let sum = bb.bvadd(&a, &b);
        bb.assert_eq(&sum, &r);
        assert_eq!(solver.solve(), SatResult::Sat);
    });

    bench_n("BV: 32-bit add SAT", 50, || {
        let mut solver = SatSolver::new();
        let a = BitVec::new_variable(&mut solver, 32);
        let b = BitVec::new_variable(&mut solver, 32);
        let r = BitVec::from_constant(&mut solver, 42, 32);
        let mut bb = BitBlaster::new(&mut solver);
        let sum = bb.bvadd(&a, &b);
        bb.assert_eq(&sum, &r);
        assert_eq!(solver.solve(), SatResult::Sat);
    });

    bench_n("BV: 8-bit mul SAT", 20, || {
        let mut solver = SatSolver::new();
        let a = BitVec::new_variable(&mut solver, 8);
        let b = BitVec::from_constant(&mut solver, 7, 8);
        let r = BitVec::from_constant(&mut solver, 21, 8);
        let mut bb = BitBlaster::new(&mut solver);
        let p = bb.bvmul(&a, &b);
        bb.assert_eq(&p, &r);
        assert_eq!(solver.solve(), SatResult::Sat);
    });

    bench_n("BV: 16-bit comparison SAT", 100, || {
        let mut solver = SatSolver::new();
        let a = BitVec::new_variable(&mut solver, 16);
        let bound = BitVec::from_constant(&mut solver, 100, 16);
        let mut bb = BitBlaster::new(&mut solver);
        let lt = bb.bvult_lit(&a, &bound);
        solver.add_clause(vec![lt]);
        assert_eq!(solver.solve(), SatResult::Sat);
    });

    bench_n("Theory: int simple (x+y=10, x-y=4)", 200, || {
        let mut smt = SmtSolver::new();
        let _ = smt.process_input(
            "(declare-const x Int)(declare-const y Int)(assert (= (+ x y) 10))(assert (= (- x y) 4))(check-sat)");
    });

    bench_n("E2E: Bool formula", 500, || {
        let mut smt = SmtSolver::new();
        let _ = smt.process_input(
            "(declare-const p Bool)(declare-const q Bool)(declare-const r Bool)(assert (or (and p q) (and (not p) r)))(assert (not (and q r)))(assert (or p q))(check-sat)");
    });

    bench_n("E2E: BV8 equation", 100, || {
        let mut smt = SmtSolver::new();
        let _ = smt.process_input(
            "(set-logic QF_BV)(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))(assert (= (bvadd x y) #x1A))(assert (= (bvsub x y) #x04))(check-sat)");
    });

    println!("\n===== END BENCHMARKS =====\n");
}

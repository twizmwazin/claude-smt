//! CDCL SAT solver
//!
//! Implements Conflict-Driven Clause Learning with:
//! - Two-watched-literal scheme for unit propagation
//! - First-UIP conflict analysis
//! - VSIDS decision heuristic
//! - Non-chronological backtracking

use std::collections::HashMap;

/// A literal is a variable (positive integer) possibly negated.
/// Positive = variable, Negative = negation.
pub type Lit = i32;
pub type Var = u32;
pub type ClauseId = usize;

#[inline]
pub fn var_of(lit: Lit) -> Var {
    lit.unsigned_abs()
}

#[inline]
pub fn sign(lit: Lit) -> bool {
    lit > 0
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LBool {
    True,
    False,
    Undef,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, Clone)]
struct Clause {
    lits: Vec<Lit>,
    learnt: bool,
}

#[derive(Debug, Clone, Copy)]
struct VarInfo {
    value: LBool,
    level: u32,
    reason: Option<ClauseId>,
}

pub struct SatSolver {
    num_vars: u32,
    clauses: Vec<Clause>,
    watches: HashMap<Lit, Vec<ClauseId>>,
    var_info: Vec<VarInfo>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,  // decision level boundaries
    activity: Vec<f64>,
    var_inc: f64,
    propagation_queue: Vec<Lit>,
    ok: bool, // set to false on top-level conflict
}

impl SatSolver {
    pub fn new() -> Self {
        SatSolver {
            num_vars: 0,
            clauses: Vec::new(),
            watches: HashMap::new(),
            var_info: vec![VarInfo {
                value: LBool::Undef,
                level: 0,
                reason: None,
            }], // index 0 unused
            trail: Vec::new(),
            trail_lim: Vec::new(),
            activity: vec![0.0], // index 0 unused
            var_inc: 1.0,
            propagation_queue: Vec::new(),
            ok: true,
        }
    }

    pub fn new_var(&mut self) -> Var {
        self.num_vars += 1;
        let v = self.num_vars;
        self.var_info.push(VarInfo {
            value: LBool::Undef,
            level: 0,
            reason: None,
        });
        self.activity.push(0.0);
        v
    }

    pub fn ensure_var(&mut self, v: Var) {
        while self.num_vars < v {
            self.new_var();
        }
    }

    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    fn value_lit(&self, lit: Lit) -> LBool {
        let v = var_of(lit);
        match self.var_info[v as usize].value {
            LBool::Undef => LBool::Undef,
            LBool::True => {
                if sign(lit) {
                    LBool::True
                } else {
                    LBool::False
                }
            }
            LBool::False => {
                if sign(lit) {
                    LBool::False
                } else {
                    LBool::True
                }
            }
        }
    }

    pub fn add_clause(&mut self, lits: Vec<Lit>) -> bool {
        // Ensure all variables exist
        for &lit in &lits {
            self.ensure_var(var_of(lit));
        }

        if lits.is_empty() {
            self.ok = false;
            return false;
        }

        if lits.len() == 1 {
            // Unit clause: enqueue directly
            if !self.enqueue(lits[0], None) {
                self.ok = false;
                return false;
            }
            return true;
        }

        let cid = self.clauses.len();
        // Watch first two literals
        self.watches.entry(Self::neg(lits[0])).or_default().push(cid);
        self.watches.entry(Self::neg(lits[1])).or_default().push(cid);

        self.clauses.push(Clause {
            lits,
            learnt: false,
        });
        true
    }

    #[inline]
    fn neg(lit: Lit) -> Lit {
        -lit
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<ClauseId>) -> bool {
        let v = var_of(lit);
        match self.value_lit(lit) {
            LBool::True => true,   // already assigned consistently
            LBool::False => false, // conflict
            LBool::Undef => {
                self.var_info[v as usize] = VarInfo {
                    value: if sign(lit) { LBool::True } else { LBool::False },
                    level: self.decision_level(),
                    reason,
                };
                self.trail.push(lit);
                self.propagation_queue.push(lit);
                true
            }
        }
    }

    /// Evaluate a literal against var_info directly (avoids borrow issues)
    fn value_lit_raw(var_info: &[VarInfo], lit: Lit) -> LBool {
        let v = var_of(lit);
        match var_info[v as usize].value {
            LBool::Undef => LBool::Undef,
            LBool::True => {
                if sign(lit) { LBool::True } else { LBool::False }
            }
            LBool::False => {
                if sign(lit) { LBool::False } else { LBool::True }
            }
        }
    }

    /// BCP (Boolean Constraint Propagation) using two-watched literals
    /// Returns None if no conflict, or Some(clause_id) of the conflicting clause
    fn propagate(&mut self) -> Option<ClauseId> {
        while let Some(p) = self.propagation_queue.pop() {
            // p just became true. Clauses watching -p (stored at watches[p])
            // need to find new watched literals since -p is now false.
            let false_lit = Self::neg(p); // the literal that became false
            let watch_list = self.watches.remove(&p).unwrap_or_default();
            let mut new_watch_list = Vec::new();
            let mut conflict = None;

            let mut i = 0;
            while i < watch_list.len() {
                let cid = watch_list[i];

                // Make sure false_lit is in position 1
                if self.clauses[cid].lits[0] == false_lit {
                    self.clauses[cid].lits.swap(0, 1);
                }

                let first_lit = self.clauses[cid].lits[0];

                // If first literal is true, clause is satisfied
                if Self::value_lit_raw(&self.var_info, first_lit) == LBool::True {
                    new_watch_list.push(cid);
                    i += 1;
                    continue;
                }

                // Look for new literal to watch
                let mut found = false;
                let clause_len = self.clauses[cid].lits.len();
                for j in 2..clause_len {
                    let lit_j = self.clauses[cid].lits[j];
                    if Self::value_lit_raw(&self.var_info, lit_j) != LBool::False {
                        self.clauses[cid].lits.swap(1, j);
                        // Watch on neg of the new literal at position 1
                        let new_watch_lit = Self::neg(self.clauses[cid].lits[1]);
                        self.watches.entry(new_watch_lit).or_default().push(cid);
                        found = true;
                        break;
                    }
                }

                if found {
                    i += 1;
                    continue;
                }

                // No replacement found - unit or conflict
                new_watch_list.push(cid);
                let unit_lit = self.clauses[cid].lits[0];
                if Self::value_lit_raw(&self.var_info, unit_lit) == LBool::False {
                    // Conflict!
                    conflict = Some(cid);
                    for &remaining in &watch_list[i + 1..] {
                        new_watch_list.push(remaining);
                    }
                    break;
                } else {
                    // Unit propagation
                    if !self.enqueue(unit_lit, Some(cid)) {
                        conflict = Some(cid);
                        for &remaining in &watch_list[i + 1..] {
                            new_watch_list.push(remaining);
                        }
                        break;
                    }
                }
                i += 1;
            }

            if !new_watch_list.is_empty() {
                self.watches.insert(p, new_watch_list);
            }

            if conflict.is_some() {
                self.propagation_queue.clear();
                return conflict;
            }
        }
        None
    }

    /// Analyze conflict using First-UIP scheme
    /// Returns (learnt clause, backtrack level)
    fn analyze(&self, conflict_cid: ClauseId) -> (Vec<Lit>, u32) {
        let mut seen = vec![false; self.num_vars as usize + 1];
        let mut learnt = Vec::new();
        let mut counter = 0;
        let mut p: Option<Lit> = None;
        let mut reason_cid = conflict_cid;
        let mut bt_level: u32 = 0;

        let trail_len = self.trail.len();
        let mut trail_idx = trail_len;

        loop {
            let clause = &self.clauses[reason_cid];
            for &lit in &clause.lits {
                if Some(lit) == p.map(Self::neg) || Some(lit) == p {
                    // skip the resolved literal (check both signs for safety)
                    if Some(var_of(lit)) == p.map(var_of) {
                        continue;
                    }
                }
                let v = var_of(lit);
                if !seen[v as usize] {
                    seen[v as usize] = true;
                    let lv = self.var_info[v as usize].level;
                    if lv == self.decision_level() {
                        counter += 1;
                    } else if lv > 0 {
                        learnt.push(lit);
                        if lv > bt_level {
                            bt_level = lv;
                        }
                    }
                }
            }

            // Find next literal on trail at current decision level
            loop {
                trail_idx -= 1;
                let trail_lit = self.trail[trail_idx];
                if seen[var_of(trail_lit) as usize] {
                    p = Some(trail_lit);
                    break;
                }
            }

            counter -= 1;
            if counter == 0 {
                break;
            }

            // Get reason for p
            let v = var_of(p.unwrap());
            reason_cid = self.var_info[v as usize].reason.unwrap();
        }

        // First literal of learnt clause is the asserting literal (negation of UIP)
        learnt.insert(0, Self::neg(p.unwrap()));

        // bt_level is the second highest decision level in the learnt clause
        // If there's only one literal (unit learnt clause), backtrack to level 0
        (learnt, bt_level)
    }

    fn backtrack(&mut self, level: u32) {
        while self.trail.len()
            > if level == 0 {
                0
            } else {
                self.trail_lim[level as usize - 1]
            }
        {
            if self.trail.is_empty() {
                break;
            }
            // Check if we'd go below the target
            let target_size = if level == 0 {
                0
            } else {
                if (level as usize - 1) < self.trail_lim.len() {
                    self.trail_lim[level as usize - 1]
                } else {
                    break;
                }
            };
            if self.trail.len() <= target_size {
                break;
            }

            let lit = self.trail.pop().unwrap();
            let v = var_of(lit);
            self.var_info[v as usize].value = LBool::Undef;
            self.var_info[v as usize].reason = None;
        }
        self.trail_lim.truncate(level as usize);
        self.propagation_queue.clear();
    }

    fn bump_activity(&mut self, v: Var) {
        self.activity[v as usize] += self.var_inc;
        if self.activity[v as usize] > 1e100 {
            // Rescale
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
    }

    fn decay_activity(&mut self) {
        self.var_inc /= 0.95;
    }

    /// Pick the unassigned variable with highest activity (VSIDS)
    fn pick_decision_var(&self) -> Option<Var> {
        let mut best: Option<Var> = None;
        let mut best_act = -1.0f64;
        for v in 1..=self.num_vars {
            if self.var_info[v as usize].value == LBool::Undef {
                if self.activity[v as usize] > best_act {
                    best_act = self.activity[v as usize];
                    best = Some(v);
                }
            }
        }
        best
    }

    fn add_learnt_clause(&mut self, lits: Vec<Lit>) {
        if lits.len() == 1 {
            self.enqueue(lits[0], None);
            return;
        }

        let cid = self.clauses.len();
        self.watches
            .entry(Self::neg(lits[0]))
            .or_default()
            .push(cid);
        self.watches
            .entry(Self::neg(lits[1]))
            .or_default()
            .push(cid);

        self.clauses.push(Clause {
            lits: lits.clone(),
            learnt: true,
        });

        // Enqueue the asserting literal
        self.enqueue(lits[0], Some(cid));
    }

    pub fn solve(&mut self) -> SatResult {
        if !self.ok {
            return SatResult::Unsat;
        }

        // Initial propagation for unit clauses
        if self.propagate().is_some() {
            return SatResult::Unsat;
        }

        loop {
            match self.propagate() {
                Some(conflict_cid) => {
                    if self.decision_level() == 0 {
                        return SatResult::Unsat;
                    }

                    let (learnt, bt_level) = self.analyze(conflict_cid);

                    // Bump activity for variables in the learnt clause
                    for &lit in &learnt {
                        self.bump_activity(var_of(lit));
                    }
                    self.decay_activity();

                    self.backtrack(bt_level);
                    self.add_learnt_clause(learnt);
                }
                None => {
                    // No conflict - make a decision
                    match self.pick_decision_var() {
                        None => return SatResult::Sat, // all variables assigned
                        Some(v) => {
                            self.trail_lim.push(self.trail.len());
                            // Decide positive polarity
                            self.enqueue(v as Lit, None);
                        }
                    }
                }
            }
        }
    }

    pub fn model_value(&self, v: Var) -> Option<bool> {
        match self.var_info.get(v as usize) {
            Some(info) => match info.value {
                LBool::True => Some(true),
                LBool::False => Some(false),
                LBool::Undef => None,
            },
            None => None,
        }
    }

    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_sat() {
        let mut solver = SatSolver::new();
        let a = solver.new_var() as Lit;
        let b = solver.new_var() as Lit;
        // (a OR b)
        solver.add_clause(vec![a, b]);
        assert_eq!(solver.solve(), SatResult::Sat);
    }

    #[test]
    fn test_simple_unsat() {
        let mut solver = SatSolver::new();
        let a = solver.new_var() as Lit;
        // a AND (NOT a)
        solver.add_clause(vec![a]);
        solver.add_clause(vec![-a]);
        assert_eq!(solver.solve(), SatResult::Unsat);
    }

    #[test]
    fn test_unit_propagation() {
        let mut solver = SatSolver::new();
        let a = solver.new_var() as Lit;
        let b = solver.new_var() as Lit;
        // a AND (NOT a OR b) => must have b
        solver.add_clause(vec![a]);
        solver.add_clause(vec![-a, b]);
        assert_eq!(solver.solve(), SatResult::Sat);
        assert_eq!(solver.model_value(1), Some(true));
        assert_eq!(solver.model_value(2), Some(true));
    }

    #[test]
    fn test_three_clause_unsat() {
        let mut solver = SatSolver::new();
        let a = solver.new_var() as Lit;
        let b = solver.new_var() as Lit;
        // (a OR b) AND (NOT a OR b) AND (NOT b) => UNSAT
        solver.add_clause(vec![a, b]);
        solver.add_clause(vec![-a, b]);
        solver.add_clause(vec![-b]);
        assert_eq!(solver.solve(), SatResult::Unsat);
    }

    #[test]
    fn test_larger_sat() {
        let mut solver = SatSolver::new();
        let x1 = solver.new_var() as Lit; // 1
        let x2 = solver.new_var() as Lit; // 2
        let x3 = solver.new_var() as Lit; // 3
        // (x1 OR x2) AND (NOT x1 OR x3) AND (NOT x2 OR NOT x3)
        solver.add_clause(vec![x1, x2]);
        solver.add_clause(vec![-x1, x3]);
        solver.add_clause(vec![-x2, -x3]);
        assert_eq!(solver.solve(), SatResult::Sat);
    }

    #[test]
    fn test_pigeonhole_2_1() {
        // 2 pigeons, 1 hole => UNSAT
        // p1h1, p2h1: pigeon 1/2 in hole 1
        let mut solver = SatSolver::new();
        let p1h1 = solver.new_var() as Lit;
        let p2h1 = solver.new_var() as Lit;
        // Each pigeon must go in hole 1
        solver.add_clause(vec![p1h1]);
        solver.add_clause(vec![p2h1]);
        // No two pigeons in same hole
        solver.add_clause(vec![-p1h1, -p2h1]);
        assert_eq!(solver.solve(), SatResult::Unsat);
    }
}

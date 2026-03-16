//! CDCL SAT solver
//!
//! Implements Conflict-Driven Clause Learning with:
//! - Two-watched-literal scheme for unit propagation
//! - First-UIP conflict analysis with reusable seen vector
//! - VSIDS decision heuristic with binary heap
//! - Non-chronological backtracking

/// A literal is a variable (positive integer) possibly negated.
/// Positive = variable, Negative = negation.
pub type Lit = i32;
pub type Var = u32;
pub type ClauseId = usize;

#[inline(always)]
pub fn var_of(lit: Lit) -> Var {
    lit.unsigned_abs()
}

#[inline(always)]
pub fn sign(lit: Lit) -> bool {
    lit > 0
}

/// Map a literal to a watch list index: positive lit l -> 2*(l-1), negative lit -l -> 2*(l-1)+1
#[inline(always)]
fn lit_index(lit: Lit) -> usize {
    if lit > 0 {
        (lit as usize - 1) * 2
    } else {
        ((-lit) as usize - 1) * 2 + 1
    }
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

/// Binary heap for VSIDS variable ordering.
/// Maintains a max-heap of unassigned variables ordered by activity.
struct VarHeap {
    heap: Vec<Var>,
    indices: Vec<usize>, // indices[v] = position in heap (usize::MAX if not in heap)
}

impl VarHeap {
    fn new() -> Self {
        VarHeap {
            heap: Vec::new(),
            indices: vec![usize::MAX], // index 0 unused
        }
    }

    fn grow_to(&mut self, n: usize) {
        while self.indices.len() <= n {
            let v = self.indices.len() as Var;
            self.indices.push(self.heap.len());
            self.heap.push(v);
        }
    }

    fn is_in_heap(&self, v: Var) -> bool {
        (v as usize) < self.indices.len() && self.indices[v as usize] != usize::MAX
    }

    fn insert(&mut self, v: Var, activity: &[f64]) {
        if self.is_in_heap(v) {
            return;
        }
        let pos = self.heap.len();
        self.heap.push(v);
        self.indices[v as usize] = pos;
        self.sift_up(pos, activity);
    }

    fn pop_max(&mut self, activity: &[f64]) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let max_var = self.heap[0];
        let last = self.heap.len() - 1;
        self.swap(0, last);
        self.indices[max_var as usize] = usize::MAX;
        self.heap.pop();
        if !self.heap.is_empty() {
            self.sift_down(0, activity);
        }
        Some(max_var)
    }

    fn update(&mut self, v: Var, activity: &[f64]) {
        if self.is_in_heap(v) {
            let pos = self.indices[v as usize];
            self.sift_up(pos, activity);
        }
    }

    fn swap(&mut self, i: usize, j: usize) {
        self.heap.swap(i, j);
        self.indices[self.heap[i] as usize] = i;
        self.indices[self.heap[j] as usize] = j;
    }

    fn sift_up(&mut self, mut pos: usize, activity: &[f64]) {
        let v = self.heap[pos];
        while pos > 0 {
            let parent = (pos - 1) / 2;
            let pv = self.heap[parent];
            if activity[v as usize] <= activity[pv as usize] {
                break;
            }
            self.swap(pos, parent);
            pos = parent;
        }
    }

    fn sift_down(&mut self, mut pos: usize, activity: &[f64]) {
        let n = self.heap.len();
        loop {
            let left = 2 * pos + 1;
            if left >= n {
                break;
            }
            let right = left + 1;
            let mut max_child = left;
            if right < n
                && activity[self.heap[right] as usize] > activity[self.heap[left] as usize]
            {
                max_child = right;
            }
            if activity[self.heap[pos] as usize] >= activity[self.heap[max_child] as usize] {
                break;
            }
            self.swap(pos, max_child);
            pos = max_child;
        }
    }
}

pub struct SatSolver {
    num_vars: u32,
    clauses: Vec<Clause>,
    /// Watch lists indexed by lit_index(lit). watches[lit_index(-l)] = clauses watching literal -l.
    watches: Vec<Vec<ClauseId>>,
    var_info: Vec<VarInfo>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    activity: Vec<f64>,
    var_inc: f64,
    propagation_queue: Vec<Lit>,
    ok: bool,
    /// Reusable seen vector for conflict analysis (avoids allocation per conflict)
    seen: Vec<bool>,
    /// VSIDS variable ordering heap
    var_heap: VarHeap,
    /// Cached false literal (set once after first new_var call)
    false_lit: Option<Lit>,
}

impl SatSolver {
    pub fn new() -> Self {
        SatSolver {
            num_vars: 0,
            clauses: Vec::new(),
            watches: Vec::new(),
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
            seen: vec![false],
            var_heap: VarHeap::new(),
            false_lit: None,
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
        self.seen.push(false);
        // Each variable has two literals: +v and -v, needing two watch list slots
        self.watches.push(Vec::new()); // for positive literal
        self.watches.push(Vec::new()); // for negative literal
        self.var_heap.grow_to(v as usize);
        v
    }

    pub fn ensure_var(&mut self, v: Var) {
        while self.num_vars < v {
            self.new_var();
        }
    }

    /// Get a literal that evaluates to false in the model. Reuses the same variable.
    /// This is a positive literal for a variable forced to false: model_value(v)=false, so lit=v evaluates false.
    pub fn get_false_lit(&mut self) -> Lit {
        if let Some(fl) = self.false_lit {
            return fl;
        }
        let v = self.new_var();
        let lit = v as Lit;
        // Force v = false
        self.add_clause(vec![-lit]);
        // The positive literal `lit` evaluates to false in the model
        self.false_lit = Some(lit);
        lit
    }

    /// Get a literal that evaluates to true in the model (negation of false var).
    pub fn get_true_lit(&mut self) -> Lit {
        -self.get_false_lit()
    }

    #[inline(always)]
    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    #[inline(always)]
    fn value_lit(&self, lit: Lit) -> LBool {
        Self::value_lit_raw(&self.var_info, lit)
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
        // Watch first two literals: watch[neg(lits[0])] and watch[neg(lits[1])]
        let idx0 = lit_index(-lits[0]);
        let idx1 = lit_index(-lits[1]);
        self.watches[idx0].push(cid);
        self.watches[idx1].push(cid);

        self.clauses.push(Clause {
            lits,
            learnt: false,
        });
        true
    }

    #[inline(always)]
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
    #[inline(always)]
    fn value_lit_raw(var_info: &[VarInfo], lit: Lit) -> LBool {
        let v = var_of(lit);
        let val = var_info[v as usize].value;
        match val {
            LBool::Undef => LBool::Undef,
            LBool::True => {
                if lit > 0 { LBool::True } else { LBool::False }
            }
            LBool::False => {
                if lit > 0 { LBool::False } else { LBool::True }
            }
        }
    }

    /// BCP (Boolean Constraint Propagation) using two-watched literals
    /// Returns None if no conflict, or Some(clause_id) of the conflicting clause
    fn propagate(&mut self) -> Option<ClauseId> {
        while let Some(p) = self.propagation_queue.pop() {
            // p just became true. Clauses watching -p (stored at watches[lit_index(p)])
            // need to find new watched literals since -p is now false.
            let false_lit = -p;
            let watch_idx = lit_index(p);

            // Take watch list to avoid borrow conflicts
            let mut watch_list = std::mem::take(&mut self.watches[watch_idx]);
            let mut i = 0;
            let mut j = 0; // compact in-place
            let mut conflict = None;

            while i < watch_list.len() {
                let cid = watch_list[i];

                // Make sure false_lit is in position 1
                if self.clauses[cid].lits[0] == false_lit {
                    self.clauses[cid].lits.swap(0, 1);
                }

                let first_lit = self.clauses[cid].lits[0];

                // If first literal is true, clause is satisfied - keep watching
                if Self::value_lit_raw(&self.var_info, first_lit) == LBool::True {
                    watch_list[j] = cid;
                    j += 1;
                    i += 1;
                    continue;
                }

                // Look for new literal to watch
                let mut found = false;
                let clause_len = self.clauses[cid].lits.len();
                for k in 2..clause_len {
                    let lit_k = self.clauses[cid].lits[k];
                    if Self::value_lit_raw(&self.var_info, lit_k) != LBool::False {
                        self.clauses[cid].lits.swap(1, k);
                        let new_watch_idx = lit_index(-self.clauses[cid].lits[1]);
                        self.watches[new_watch_idx].push(cid);
                        found = true;
                        break;
                    }
                }

                if found {
                    i += 1;
                    continue;
                }

                // No replacement found - unit or conflict: keep watching
                watch_list[j] = cid;
                j += 1;
                let unit_lit = first_lit;
                if Self::value_lit_raw(&self.var_info, unit_lit) == LBool::False {
                    // Conflict! Copy remaining watches
                    conflict = Some(cid);
                    while i + 1 < watch_list.len() {
                        i += 1;
                        watch_list[j] = watch_list[i];
                        j += 1;
                    }
                    break;
                } else {
                    // Unit propagation
                    if !self.enqueue(unit_lit, Some(cid)) {
                        conflict = Some(cid);
                        while i + 1 < watch_list.len() {
                            i += 1;
                            watch_list[j] = watch_list[i];
                            j += 1;
                        }
                        break;
                    }
                }
                i += 1;
            }

            watch_list.truncate(j);
            self.watches[watch_idx] = watch_list;

            if conflict.is_some() {
                self.propagation_queue.clear();
                return conflict;
            }
        }
        None
    }

    /// Analyze conflict using First-UIP scheme
    /// Returns (learnt clause, backtrack level)
    fn analyze(&mut self, conflict_cid: ClauseId) -> (Vec<Lit>, u32) {
        // Track all variables we mark as seen, for efficient cleanup
        let mut seen_vars: Vec<Var> = Vec::new();
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
                if Some(var_of(lit)) == p.map(var_of) {
                    continue;
                }
                let v = var_of(lit);
                if !self.seen[v as usize] {
                    self.seen[v as usize] = true;
                    seen_vars.push(v);
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
                if self.seen[var_of(trail_lit) as usize] {
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

        // Clean up seen vector
        for v in seen_vars {
            self.seen[v as usize] = false;
        }

        (learnt, bt_level)
    }

    fn backtrack(&mut self, level: u32) {
        if self.decision_level() <= level {
            return;
        }
        let target_size = if level == 0 {
            // Preserve level 0 assignments (unit propagations)
            if self.trail_lim.is_empty() {
                return;
            }
            self.trail_lim[0]
        } else if (level as usize - 1) < self.trail_lim.len() {
            self.trail_lim[level as usize - 1]
        } else {
            return;
        };

        while self.trail.len() > target_size {
            let lit = self.trail.pop().unwrap();
            let v = var_of(lit);
            self.var_info[v as usize].value = LBool::Undef;
            self.var_info[v as usize].reason = None;
            self.var_heap.insert(v, &self.activity);
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
        // Update heap position after activity change
        self.var_heap.update(v, &self.activity);
    }

    fn decay_activity(&mut self) {
        self.var_inc /= 0.95;
    }

    /// Pick the unassigned variable with highest activity (VSIDS) using binary heap
    fn pick_decision_var(&mut self) -> Option<Var> {
        loop {
            match self.var_heap.pop_max(&self.activity) {
                None => return None,
                Some(v) => {
                    if self.var_info[v as usize].value == LBool::Undef {
                        return Some(v);
                    }
                    // Variable already assigned, skip it
                }
            }
        }
    }

    fn add_learnt_clause(&mut self, lits: Vec<Lit>) {
        if lits.len() == 1 {
            self.enqueue(lits[0], None);
            return;
        }

        let cid = self.clauses.len();
        let idx0 = lit_index(-lits[0]);
        let idx1 = lit_index(-lits[1]);
        self.watches[idx0].push(cid);
        self.watches[idx1].push(cid);

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
                        None => return SatResult::Sat,
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

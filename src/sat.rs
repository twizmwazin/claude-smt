//! CDCL SAT solver
//!
//! Implements Conflict-Driven Clause Learning with:
//! - Two-watched-literal scheme for unit propagation
//! - First-UIP conflict analysis with learned clause minimization
//! - VSIDS decision heuristic with binary heap
//! - Phase saving for decision polarity
//! - Luby restarts
//! - Clause database management (periodic reduction of learnt clauses)
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
    activity: f32,
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

/// Compute Luby sequence value for index i (1-indexed)
fn luby(mut i: u32) -> u32 {
    // Find the finite subsequence that i is in
    let mut size: u32 = 1;
    let mut seq: u32 = 0;
    while size < i + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    // Now find the element
    while size - 1 != i {
        size = (size - 1) >> 1;
        seq -= 1;
        if i >= size {
            i -= size;
        }
    }
    1u32 << seq
}

pub struct SatSolver {
    num_vars: u32,
    clauses: Vec<Clause>,
    num_original_clauses: usize,
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
    /// Phase saving: saved polarity for each variable (true = positive, false = negative)
    phase: Vec<bool>,
    /// Number of conflicts seen so far
    num_conflicts: u64,
    /// Clause activity increment for learnt clause management
    clause_inc: f32,
    /// Number of learnt clauses at the start of current restart cycle
    max_learnts: f64,
}

impl SatSolver {
    pub fn new() -> Self {
        SatSolver {
            num_vars: 0,
            clauses: Vec::new(),
            num_original_clauses: 0,
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
            phase: vec![false], // index 0 unused
            num_conflicts: 0,
            clause_inc: 1.0,
            max_learnts: 0.0,
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
        self.phase.push(false); // default: decide negative (false) - better for UNSAT
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
            activity: 0.0,
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

    /// Check if a literal can be removed from the learned clause via self-subsumption.
    /// A literal is redundant if its reason clause only contains literals that are
    /// either at level 0 or already in the learned clause (marked as seen).
    /// Analyze conflict using First-UIP scheme with learned clause minimization.
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
            // Bump activity of clause involved in conflict
            if self.clauses[reason_cid].learnt {
                self.clauses[reason_cid].activity += self.clause_inc;
            }

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

        // Put the literal with highest level at position 1 (for watch list)
        if learnt.len() > 2 {
            let mut max_idx = 1;
            for i in 2..learnt.len() {
                let lv = self.var_info[var_of(learnt[i]) as usize].level;
                if lv > self.var_info[var_of(learnt[max_idx]) as usize].level {
                    max_idx = i;
                }
            }
            learnt.swap(1, max_idx);
            bt_level = self.var_info[var_of(learnt[1]) as usize].level;
        }
        let minimized = learnt;

        // Clean up seen vector
        for v in seen_vars {
            self.seen[v as usize] = false;
        }

        (minimized, bt_level)
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
            // Phase saving: remember the polarity this variable was assigned
            self.phase[v as usize] = sign(lit);
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

    fn decay_clause_activity(&mut self) {
        self.clause_inc /= 0.999;
    }

    /// Pick the unassigned variable with highest activity (VSIDS) using binary heap
    /// Uses phase saving for polarity decision
    fn pick_decision_var(&mut self) -> Option<Lit> {
        loop {
            match self.var_heap.pop_max(&self.activity) {
                None => return None,
                Some(v) => {
                    if self.var_info[v as usize].value == LBool::Undef {
                        // Phase saving: use saved polarity
                        let lit = if self.phase[v as usize] {
                            v as Lit
                        } else {
                            -(v as Lit)
                        };
                        return Some(lit);
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
            activity: 0.0,
        });

        // Enqueue the asserting literal
        self.enqueue(lits[0], Some(cid));
    }

    /// Reduce the clause database by removing half of the low-activity learnt clauses
    fn reduce_db(&mut self) {
        // Collect indices of learnt clauses that are not locked (not a reason for a current assignment)
        let mut removable: Vec<(ClauseId, f32)> = Vec::new();
        for (cid, clause) in self.clauses.iter().enumerate() {
            if clause.learnt && !self.is_clause_locked(cid) {
                removable.push((cid, clause.activity));
            }
        }

        if removable.len() < 10 {
            return; // not worth reducing
        }

        // Sort by activity (lowest first)
        removable.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));

        // Remove the bottom half
        let remove_count = removable.len() / 2;
        let mut to_remove = vec![false; self.clauses.len()];
        for i in 0..remove_count {
            to_remove[removable[i].0] = true;
        }

        // Remove watches for deleted clauses and rebuild watch lists
        let mut new_clauses: Vec<Clause> = Vec::with_capacity(self.clauses.len());
        let mut id_map: Vec<Option<ClauseId>> = vec![None; self.clauses.len()];

        for (old_id, clause) in self.clauses.drain(..).enumerate() {
            if to_remove[old_id] {
                continue;
            }
            let new_id = new_clauses.len();
            id_map[old_id] = Some(new_id);
            new_clauses.push(clause);
        }
        self.clauses = new_clauses;

        // Rebuild all watch lists
        for w in &mut self.watches {
            w.clear();
        }
        for (cid, clause) in self.clauses.iter().enumerate() {
            if clause.lits.len() >= 2 {
                let idx0 = lit_index(-clause.lits[0]);
                let idx1 = lit_index(-clause.lits[1]);
                self.watches[idx0].push(cid);
                self.watches[idx1].push(cid);
            }
        }

        // Update reason references in var_info
        for vi in &mut self.var_info {
            if let Some(old_reason) = vi.reason {
                vi.reason = id_map.get(old_reason).copied().flatten();
            }
        }
    }

    /// Check if a learnt clause is locked (used as a reason for some current assignment)
    fn is_clause_locked(&self, cid: ClauseId) -> bool {
        let clause = &self.clauses[cid];
        if clause.lits.is_empty() {
            return false;
        }
        let first_lit = clause.lits[0];
        let v = var_of(first_lit);
        if self.var_info[v as usize].value != LBool::Undef {
            if let Some(reason) = self.var_info[v as usize].reason {
                return reason == cid;
            }
        }
        false
    }

    pub fn solve(&mut self) -> SatResult {
        if !self.ok {
            return SatResult::Unsat;
        }

        // Initial propagation for unit clauses
        if self.propagate().is_some() {
            return SatResult::Unsat;
        }

        // Record number of original clauses for clause DB management
        self.num_original_clauses = self.clauses.len();
        self.max_learnts = (self.num_original_clauses as f64 / 3.0).max(10.0);

        let mut restart_count: u32 = 0;
        let base_restart_interval: u32 = 32;

        loop {
            // Restart check
            let restart_limit = base_restart_interval.saturating_mul(luby(restart_count));
            let mut conflicts_in_restart: u32 = 0;

            loop {
                match self.propagate() {
                    Some(conflict_cid) => {
                        if self.decision_level() == 0 {
                            return SatResult::Unsat;
                        }

                        self.num_conflicts += 1;
                        conflicts_in_restart += 1;

                        let (learnt, bt_level) = self.analyze(conflict_cid);

                        // Bump activity for variables in the learnt clause
                        for &lit in &learnt {
                            self.bump_activity(var_of(lit));
                        }
                        self.decay_activity();
                        self.decay_clause_activity();

                        self.backtrack(bt_level);
                        self.add_learnt_clause(learnt);

                        // Note: clause DB reduction happens during restarts at level 0

                        // Check restart
                        if conflicts_in_restart >= restart_limit {
                            break; // trigger restart
                        }
                    }
                    None => {
                        // No conflict - make a decision
                        match self.pick_decision_var() {
                            None => return SatResult::Sat,
                            Some(decision_lit) => {
                                self.trail_lim.push(self.trail.len());
                                self.enqueue(decision_lit, None);
                            }
                        }
                    }
                }
            }

            // Restart: backtrack to level 0
            restart_count += 1;
            self.backtrack(0);

            // Clause database reduction at level 0
            let num_learnt = self.clauses.len().saturating_sub(self.num_original_clauses);
            if num_learnt as f64 > self.max_learnts {
                self.reduce_db();
                self.max_learnts *= 1.1;
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

    #[test]
    fn test_luby_sequence() {
        // Luby sequence: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
        assert_eq!(luby(0), 1);
        assert_eq!(luby(1), 1);
        assert_eq!(luby(2), 2);
        assert_eq!(luby(3), 1);
        assert_eq!(luby(4), 1);
        assert_eq!(luby(5), 2);
        assert_eq!(luby(6), 4);
    }

    #[test]
    fn test_pigeonhole_4_3() {
        // 4 pigeons, 3 holes => UNSAT
        let mut solver = SatSolver::new();
        let n = 4;
        let holes = 3;
        let mut vars = vec![vec![0i32; holes]; n];
        for i in 0..n {
            for j in 0..holes {
                vars[i][j] = solver.new_var() as Lit;
            }
        }
        // Each pigeon in at least one hole
        for i in 0..n {
            solver.add_clause(vars[i].clone());
        }
        // No two pigeons in same hole
        for j in 0..holes {
            for i1 in 0..n {
                for i2 in (i1 + 1)..n {
                    solver.add_clause(vec![-vars[i1][j], -vars[i2][j]]);
                }
            }
        }
        assert_eq!(solver.solve(), SatResult::Unsat);
    }

    #[test]
    fn test_pigeonhole_5_4() {
        // 5 pigeons, 4 holes => UNSAT (harder, needs restarts)
        let mut solver = SatSolver::new();
        let n = 5;
        let holes = 4;
        let mut vars = vec![vec![0i32; holes]; n];
        for i in 0..n {
            for j in 0..holes {
                vars[i][j] = solver.new_var() as Lit;
            }
        }
        for i in 0..n {
            solver.add_clause(vars[i].clone());
        }
        for j in 0..holes {
            for i1 in 0..n {
                for i2 in (i1 + 1)..n {
                    solver.add_clause(vec![-vars[i1][j], -vars[i2][j]]);
                }
            }
        }
        assert_eq!(solver.solve(), SatResult::Unsat);
    }
}

//! Theory solver for Int, Real, and String sorts.
//!
//! Uses direct constraint evaluation: terms are evaluated to concrete values,
//! and constraints are checked for satisfiability by searching over possible
//! assignments to theory variables.

use std::collections::HashMap;

use crate::ast::{Sort, Term};

/// A concrete value in the theory solver
#[derive(Debug, Clone, PartialEq)]
pub enum TheoryValue {
    Int(i64),
    Real(f64),
    Str(String),
    Bool(bool),
}

impl std::fmt::Display for TheoryValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TheoryValue::Int(n) => {
                if *n < 0 {
                    write!(f, "(- {})", -n)
                } else {
                    write!(f, "{}", n)
                }
            }
            TheoryValue::Real(v) => {
                if *v < 0.0 {
                    write!(f, "(- {})", -v)
                } else {
                    write!(f, "{}", format_real(*v))
                }
            }
            TheoryValue::Str(s) => write!(f, "\"{}\"", s),
            TheoryValue::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
        }
    }
}

fn format_real(v: f64) -> String {
    if v == v.floor() && v.is_finite() {
        format!("{:.1}", v)
    } else {
        format!("{}", v)
    }
}

/// Theory variable info
#[derive(Debug, Clone)]
pub struct TheoryVar {
    pub sort: Sort,
    pub value: Option<TheoryValue>,
}

/// A constraint in the theory solver
#[derive(Debug, Clone)]
pub struct Constraint {
    pub term: Term,
    pub expected: bool,
}

/// Theory solver that handles Int, Real, and String theories
pub struct TheorySolver {
    pub variables: HashMap<String, TheoryVar>,
    constraints: Vec<Constraint>,
    defined_funs: HashMap<String, (Vec<(String, Sort)>, Term)>,
}

impl TheorySolver {
    pub fn new() -> Self {
        TheorySolver {
            variables: HashMap::new(),
            constraints: Vec::new(),
            defined_funs: HashMap::new(),
        }
    }

    pub fn declare_variable(&mut self, name: &str, sort: &Sort) {
        self.variables.insert(
            name.to_string(),
            TheoryVar {
                sort: sort.clone(),
                value: None,
            },
        );
    }

    pub fn define_fun(&mut self, name: String, params: Vec<(String, Sort)>, body: Term) {
        self.defined_funs.insert(name, (params, body));
    }

    pub fn add_constraint(&mut self, term: Term, expected: bool) {
        self.constraints.push(Constraint { term, expected });
    }

    pub fn reset(&mut self) {
        self.variables.clear();
        self.constraints.clear();
        self.defined_funs.clear();
    }

    /// Check if current constraints are satisfiable.
    /// Uses a search over free theory variables.
    pub fn check_sat(&mut self) -> SatStatus {
        // Try to solve simple equality constraints directly first
        if self.try_direct_solve() {
            if self.check_all_constraints() {
                return SatStatus::Sat;
            }
            // Direct solve assigned values but constraints failed, clear and try search
            for (_, var) in self.variables.iter_mut() {
                var.value = None;
            }
        }

        // Collect free (unassigned) theory variables
        let free_vars: Vec<(String, Sort)> = self
            .variables
            .iter()
            .filter(|(_, v)| v.value.is_none())
            .map(|(name, v)| (name.clone(), v.sort.clone()))
            .collect();

        if free_vars.is_empty() {
            // All variables assigned, just check constraints
            return if self.check_all_constraints() {
                SatStatus::Sat
            } else {
                SatStatus::Unsat
            };
        }

        // Search over possible values for free variables
        if self.search_assignment(&free_vars, 0) {
            SatStatus::Sat
        } else {
            SatStatus::Unsat
        }
    }

    /// Try to solve simple equality constraints directly without search.
    /// Returns true if it assigned all variables, false otherwise.
    fn try_direct_solve(&mut self) -> bool {
        let mut changed = true;
        while changed {
            changed = false;
            for ci in 0..self.constraints.len() {
                if !self.constraints[ci].expected {
                    continue;
                }
                let term = self.constraints[ci].term.clone();
                if let Term::Eq(ref a, ref b) = term {
                    // x = <expr> or <expr> = x
                    if let Some((var_name, expr)) = self.extract_var_eq(a, b) {
                        if self.variables.get(&var_name).and_then(|v| v.value.as_ref()).is_some() {
                            continue; // already assigned
                        }
                        // Try to evaluate the expression
                        if let Some(val) = self.eval_value(expr) {
                            self.variables.get_mut(&var_name).unwrap().value = Some(val);
                            changed = true;
                        }
                    }
                }
            }
        }
        // Check if all variables got assigned
        self.variables.values().all(|v| v.value.is_some())
    }

    /// Extract (variable_name, expression) from an equality if one side is a variable
    fn extract_var_eq<'b>(&self, a: &'b Term, b: &'b Term) -> Option<(String, &'b Term)> {
        if let Term::Variable(name) = a {
            if self.variables.contains_key(name) {
                return Some((name.clone(), b));
            }
        }
        if let Term::Variable(name) = b {
            if self.variables.contains_key(name) {
                return Some((name.clone(), a));
            }
        }
        None
    }

    fn search_assignment(&mut self, free_vars: &[(String, Sort)], idx: usize) -> bool {
        if idx >= free_vars.len() {
            return self.check_all_constraints();
        }

        // Early pruning: check constraints that are fully evaluable with current assignment
        if !self.check_partial_constraints() {
            return false;
        }

        let (name, sort) = &free_vars[idx];
        let candidates = self.generate_candidates(name, sort);

        for val in candidates {
            self.variables.get_mut(name).unwrap().value = Some(val);
            if self.search_assignment(free_vars, idx + 1) {
                return true;
            }
        }
        self.variables.get_mut(name).unwrap().value = None;
        false
    }

    /// Check constraints that can be fully evaluated with current partial assignment.
    /// Returns false if any fully-evaluable constraint is violated (prune early).
    fn check_partial_constraints(&self) -> bool {
        for c in &self.constraints {
            if let Some(v) = self.eval_bool(&c.term) {
                if v != c.expected {
                    return false;
                }
            }
        }
        true
    }

    /// Generate candidate values for a variable based on constraints
    fn generate_candidates(&self, name: &str, sort: &Sort) -> Vec<TheoryValue> {
        // Extract hints from constraints that mention this variable
        let mut candidates = Vec::new();

        match sort {
            Sort::Int => {
                // Collect integer constants from constraints
                let mut ints: Vec<i64> = Vec::new();
                for c in &self.constraints {
                    self.collect_int_hints(&c.term, name, &mut ints);
                }
                ints.sort();
                ints.dedup();
                if ints.is_empty() {
                    ints = vec![0, 1, -1, 2, -2, 3, 5, 10, 42, 100];
                }
                // Also try values around collected hints, negations, differences, quotients
                let mut expanded = ints.clone();
                for &v in &ints {
                    for delta in [-3, -2, -1, 1, 2, 3] {
                        expanded.push(v + delta);
                    }
                    expanded.push(-v); // negation
                }
                // Try differences and quotients between pairs
                for i in 0..ints.len() {
                    for j in 0..ints.len() {
                        if i != j {
                            expanded.push(ints[i] - ints[j]);
                            expanded.push(ints[i] + ints[j]);
                            if ints[j] != 0 && ints[i] % ints[j] == 0 {
                                expanded.push(ints[i] / ints[j]);
                            }
                            // Also try product (for solving division constraints)
                            if let Some(p) = ints[i].checked_mul(ints[j]) {
                                expanded.push(p);
                            }
                        }
                    }
                }
                expanded.sort();
                expanded.dedup();
                candidates = expanded.into_iter().map(TheoryValue::Int).collect();
            }
            Sort::Real => {
                let mut reals: Vec<f64> = Vec::new();
                for c in &self.constraints {
                    self.collect_real_hints(&c.term, name, &mut reals);
                }
                reals.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
                reals.dedup_by(|a, b| (*a - *b).abs() < 1e-10);
                if reals.is_empty() {
                    reals = vec![0.0, 1.0, -1.0, 0.5, 2.0, 3.14, -0.5];
                }
                let mut expanded = reals.clone();
                for &v in &reals {
                    expanded.push(v - 1.0);
                    expanded.push(v + 1.0);
                    expanded.push(v / 2.0);
                }
                expanded.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
                expanded.dedup_by(|a, b| (*a - *b).abs() < 1e-10);
                candidates = expanded.into_iter().map(TheoryValue::Real).collect();
            }
            Sort::String => {
                let mut strings: Vec<String> = Vec::new();
                for c in &self.constraints {
                    self.collect_string_hints(&c.term, &mut strings);
                }
                strings.sort();
                strings.dedup();
                if strings.is_empty() {
                    strings = vec!["".into(), "a".into(), "b".into(), "hello".into()];
                }
                // Also try substrings and concatenations
                let mut expanded = strings.clone();
                for s in &strings {
                    for i in 0..s.len() {
                        for j in (i + 1)..=s.len() {
                            expanded.push(s[i..j].to_string());
                        }
                    }
                }
                expanded.push("".into());
                expanded.sort();
                expanded.dedup();
                candidates = expanded.into_iter().map(TheoryValue::Str).collect();
            }
            _ => {}
        }

        candidates
    }

    fn collect_int_hints(&self, term: &Term, _var_name: &str, hints: &mut Vec<i64>) {
        match term {
            Term::IntLiteral(n) => hints.push(*n),
            Term::RealLiteral(n, d) => hints.push(*n / *d),
            Term::Eq(a, b) | Term::Lt(a, b) | Term::Le(a, b)
            | Term::Gt(a, b) | Term::Ge(a, b) | Term::Sub(a, b)
            | Term::Div(a, b) | Term::Mod(a, b) | Term::Distinct(a, b) => {
                self.collect_int_hints(a, _var_name, hints);
                self.collect_int_hints(b, _var_name, hints);
            }
            Term::Add(ts) | Term::Mul(ts) => {
                for t in ts {
                    self.collect_int_hints(t, _var_name, hints);
                }
            }
            Term::Neg(t) => {
                self.collect_int_hints(t, _var_name, hints);
                // Also add negated values of sub-hints
                let mut sub_hints = Vec::new();
                self.collect_int_hints(t, _var_name, &mut sub_hints);
                for h in sub_hints {
                    hints.push(-h);
                }
            }
            Term::Abs(t) | Term::ToInt(t) => {
                self.collect_int_hints(t, _var_name, hints);
            }
            Term::Ite(c, t, e) => {
                self.collect_int_hints(c, _var_name, hints);
                self.collect_int_hints(t, _var_name, hints);
                self.collect_int_hints(e, _var_name, hints);
            }
            Term::Not(t) => self.collect_int_hints(t, _var_name, hints),
            Term::And(ts) | Term::Or(ts) => {
                for t in ts {
                    self.collect_int_hints(t, _var_name, hints);
                }
            }
            Term::StrLen(t) => self.collect_int_hints(t, _var_name, hints),
            Term::StrToInt(t) => self.collect_int_hints(t, _var_name, hints),
            Term::Let { bindings, body } => {
                for (_, val) in bindings {
                    self.collect_int_hints(val, _var_name, hints);
                }
                self.collect_int_hints(body, _var_name, hints);
            }
            _ => {}
        }
    }

    fn collect_real_hints(&self, term: &Term, _var_name: &str, hints: &mut Vec<f64>) {
        match term {
            Term::IntLiteral(n) => hints.push(*n as f64),
            Term::RealLiteral(n, d) => hints.push(*n as f64 / *d as f64),
            Term::Eq(a, b) | Term::Lt(a, b) | Term::Le(a, b)
            | Term::Gt(a, b) | Term::Ge(a, b) | Term::Sub(a, b)
            | Term::Div(a, b) | Term::Distinct(a, b) => {
                self.collect_real_hints(a, _var_name, hints);
                self.collect_real_hints(b, _var_name, hints);
            }
            Term::Add(ts) | Term::Mul(ts) => {
                for t in ts {
                    self.collect_real_hints(t, _var_name, hints);
                }
            }
            Term::Neg(t) | Term::Abs(t) | Term::ToReal(t) => {
                self.collect_real_hints(t, _var_name, hints);
            }
            Term::Not(t) => self.collect_real_hints(t, _var_name, hints),
            Term::And(ts) | Term::Or(ts) => {
                for t in ts {
                    self.collect_real_hints(t, _var_name, hints);
                }
            }
            _ => {}
        }
    }

    fn collect_string_hints(&self, term: &Term, hints: &mut Vec<String>) {
        match term {
            Term::StringLiteral(s) => hints.push(s.clone()),
            Term::Eq(a, b) | Term::Distinct(a, b) | Term::StrContains(a, b)
            | Term::StrPrefixOf(a, b) | Term::StrSuffixOf(a, b)
            | Term::StrLt(a, b) | Term::StrLe(a, b) => {
                self.collect_string_hints(a, hints);
                self.collect_string_hints(b, hints);
            }
            Term::StrConcat(ts) => {
                for t in ts {
                    self.collect_string_hints(t, hints);
                }
            }
            Term::StrAt(s, _) => self.collect_string_hints(s, hints),
            Term::StrSubstr(s, _, _) => self.collect_string_hints(s, hints),
            Term::StrIndexOf(s, t, _) => {
                self.collect_string_hints(s, hints);
                self.collect_string_hints(t, hints);
            }
            Term::StrReplace(s, a, b) => {
                self.collect_string_hints(s, hints);
                self.collect_string_hints(a, hints);
                self.collect_string_hints(b, hints);
            }
            Term::IntToStr(t) => self.collect_string_hints(t, hints),
            Term::Not(t) => self.collect_string_hints(t, hints),
            Term::And(ts) | Term::Or(ts) => {
                for t in ts {
                    self.collect_string_hints(t, hints);
                }
            }
            Term::Ite(c, t, e) => {
                self.collect_string_hints(c, hints);
                self.collect_string_hints(t, hints);
                self.collect_string_hints(e, hints);
            }
            Term::Let { bindings, body } => {
                for (_, val) in bindings {
                    self.collect_string_hints(val, hints);
                }
                self.collect_string_hints(body, hints);
            }
            _ => {}
        }
    }

    fn check_all_constraints(&self) -> bool {
        for c in &self.constraints {
            match self.eval_bool(&c.term) {
                Some(v) => {
                    if v != c.expected {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    }

    /// Evaluate a term to a boolean value
    pub fn eval_bool(&self, term: &Term) -> Option<bool> {
        match term {
            Term::True => Some(true),
            Term::False => Some(false),
            Term::Variable(name) => {
                if let Some((params, body)) = self.defined_funs.get(name) {
                    if params.is_empty() {
                        return self.eval_bool(&body);
                    }
                }
                match self.variables.get(name)?.value.as_ref()? {
                    TheoryValue::Bool(b) => Some(*b),
                    _ => None,
                }
            }
            Term::Not(t) => Some(!self.eval_bool(t)?),
            Term::And(ts) => {
                for t in ts {
                    if !self.eval_bool(t)? {
                        return Some(false);
                    }
                }
                Some(true)
            }
            Term::Or(ts) => {
                for t in ts {
                    if self.eval_bool(t)? {
                        return Some(true);
                    }
                }
                Some(false)
            }
            Term::Xor(a, b) => Some(self.eval_bool(a)? != self.eval_bool(b)?),
            Term::Implies(a, b) => Some(!self.eval_bool(a)? || self.eval_bool(b)?),
            Term::Eq(a, b) => {
                // Try each type
                if let (Some(va), Some(vb)) = (self.eval_int(a), self.eval_int(b)) {
                    return Some(va == vb);
                }
                if let (Some(va), Some(vb)) = (self.eval_real(a), self.eval_real(b)) {
                    return Some((va - vb).abs() < 1e-10);
                }
                if let (Some(va), Some(vb)) = (self.eval_string(a), self.eval_string(b)) {
                    return Some(va == vb);
                }
                if let (Some(va), Some(vb)) = (self.eval_bool(a), self.eval_bool(b)) {
                    return Some(va == vb);
                }
                None
            }
            Term::Distinct(a, b) => {
                let eq = self.eval_bool(&Term::Eq(Box::new(a.as_ref().clone()), Box::new(b.as_ref().clone())))?;
                Some(!eq)
            }
            Term::Lt(a, b) => {
                if let (Some(va), Some(vb)) = (self.eval_int(a), self.eval_int(b)) {
                    return Some(va < vb);
                }
                if let (Some(va), Some(vb)) = (self.eval_real(a), self.eval_real(b)) {
                    return Some(va < vb);
                }
                None
            }
            Term::Le(a, b) => {
                if let (Some(va), Some(vb)) = (self.eval_int(a), self.eval_int(b)) {
                    return Some(va <= vb);
                }
                if let (Some(va), Some(vb)) = (self.eval_real(a), self.eval_real(b)) {
                    return Some(va <= vb);
                }
                None
            }
            Term::Gt(a, b) => {
                if let (Some(va), Some(vb)) = (self.eval_int(a), self.eval_int(b)) {
                    return Some(va > vb);
                }
                if let (Some(va), Some(vb)) = (self.eval_real(a), self.eval_real(b)) {
                    return Some(va > vb);
                }
                None
            }
            Term::Ge(a, b) => {
                if let (Some(va), Some(vb)) = (self.eval_int(a), self.eval_int(b)) {
                    return Some(va >= vb);
                }
                if let (Some(va), Some(vb)) = (self.eval_real(a), self.eval_real(b)) {
                    return Some(va >= vb);
                }
                None
            }
            Term::IsInt(t) => {
                let v = self.eval_real(t)?;
                Some((v - v.round()).abs() < 1e-10)
            }
            Term::Divisible(n, t) => {
                let v = self.eval_int(t)?;
                Some(v % (*n as i64) == 0)
            }
            Term::StrContains(a, b) => {
                let sa = self.eval_string(a)?;
                let sb = self.eval_string(b)?;
                Some(sa.contains(&sb))
            }
            Term::StrPrefixOf(a, b) => {
                let sa = self.eval_string(a)?;
                let sb = self.eval_string(b)?;
                Some(sb.starts_with(&sa))
            }
            Term::StrSuffixOf(a, b) => {
                let sa = self.eval_string(a)?;
                let sb = self.eval_string(b)?;
                Some(sb.ends_with(&sa))
            }
            Term::StrLt(a, b) => {
                let sa = self.eval_string(a)?;
                let sb = self.eval_string(b)?;
                Some(sa < sb)
            }
            Term::StrLe(a, b) => {
                let sa = self.eval_string(a)?;
                let sb = self.eval_string(b)?;
                Some(sa <= sb)
            }
            Term::Ite(c, t, e) => {
                if self.eval_bool(c)? {
                    self.eval_bool(t)
                } else {
                    self.eval_bool(e)
                }
            }
            Term::Let { bindings, body } => {
                // For evaluation, we need to handle let bindings
                // This is a simplified approach - clone and substitute
                let substituted = self.substitute_let(bindings, body);
                self.eval_bool(&substituted)
            }
            _ => None,
        }
    }

    /// Evaluate a term to an integer value
    pub fn eval_int(&self, term: &Term) -> Option<i64> {
        match term {
            Term::IntLiteral(n) => Some(*n),
            Term::RealLiteral(n, d) => {
                if *n % *d == 0 {
                    Some(*n / *d)
                } else {
                    None
                }
            }
            Term::Variable(name) => {
                if let Some((params, body)) = self.defined_funs.get(name) {
                    if params.is_empty() {
                        return self.eval_int(&body);
                    }
                }
                match self.variables.get(name)?.value.as_ref()? {
                    TheoryValue::Int(n) => Some(*n),
                    _ => None,
                }
            }
            Term::Neg(t) => Some(-self.eval_int(t)?),
            Term::Add(ts) => {
                let mut sum = 0i64;
                for t in ts {
                    sum = sum.checked_add(self.eval_int(t)?)?;
                }
                Some(sum)
            }
            Term::Sub(a, b) => {
                let va = self.eval_int(a)?;
                let vb = self.eval_int(b)?;
                va.checked_sub(vb)
            }
            Term::Mul(ts) => {
                let mut prod = 1i64;
                for t in ts {
                    prod = prod.checked_mul(self.eval_int(t)?)?;
                }
                Some(prod)
            }
            Term::Div(a, b) => {
                let va = self.eval_int(a)?;
                let vb = self.eval_int(b)?;
                if vb == 0 { return None; }
                // SMT-LIB integer division: Euclidean
                Some(euclidean_div(va, vb))
            }
            Term::Mod(a, b) => {
                let va = self.eval_int(a)?;
                let vb = self.eval_int(b)?;
                if vb == 0 { return None; }
                Some(euclidean_mod(va, vb))
            }
            Term::Abs(t) => Some(self.eval_int(t)?.abs()),
            Term::ToInt(t) => {
                let v = self.eval_real(t)?;
                Some(v.floor() as i64)
            }
            Term::StrLen(t) => {
                let s = self.eval_string(t)?;
                Some(s.len() as i64)
            }
            Term::StrToInt(t) => {
                let s = self.eval_string(t)?;
                match s.parse::<i64>() {
                    Ok(n) if n >= 0 => Some(n),
                    _ => Some(-1), // SMT-LIB spec
                }
            }
            Term::StrIndexOf(s, t, i) => {
                let ss = self.eval_string(s)?;
                let st = self.eval_string(t)?;
                let si = self.eval_int(i)? as usize;
                if si > ss.len() { return Some(-1); }
                match ss[si..].find(&st) {
                    Some(pos) => Some((si + pos) as i64),
                    None => Some(-1),
                }
            }
            Term::Ite(c, t, e) => {
                if self.eval_bool(c)? {
                    self.eval_int(t)
                } else {
                    self.eval_int(e)
                }
            }
            Term::Let { bindings, body } => {
                let substituted = self.substitute_let(bindings, body);
                self.eval_int(&substituted)
            }
            _ => None,
        }
    }

    /// Evaluate a term to a real value
    pub fn eval_real(&self, term: &Term) -> Option<f64> {
        match term {
            Term::IntLiteral(n) => Some(*n as f64),
            Term::RealLiteral(n, d) => Some(*n as f64 / *d as f64),
            Term::Variable(name) => {
                if let Some((params, body)) = self.defined_funs.get(name) {
                    if params.is_empty() {
                        return self.eval_real(&body);
                    }
                }
                match self.variables.get(name)?.value.as_ref()? {
                    TheoryValue::Real(v) => Some(*v),
                    TheoryValue::Int(n) => Some(*n as f64),
                    _ => None,
                }
            }
            Term::Neg(t) => Some(-self.eval_real(t)?),
            Term::Add(ts) => {
                let mut sum = 0.0f64;
                for t in ts {
                    sum += self.eval_real(t)?;
                }
                Some(sum)
            }
            Term::Sub(a, b) => Some(self.eval_real(a)? - self.eval_real(b)?),
            Term::Mul(ts) => {
                let mut prod = 1.0f64;
                for t in ts {
                    prod *= self.eval_real(t)?;
                }
                Some(prod)
            }
            Term::Div(a, b) => {
                let va = self.eval_real(a)?;
                let vb = self.eval_real(b)?;
                if vb.abs() < 1e-15 { return None; }
                Some(va / vb)
            }
            Term::Abs(t) => Some(self.eval_real(t)?.abs()),
            Term::ToReal(t) => {
                let v = self.eval_int(t)?;
                Some(v as f64)
            }
            Term::Ite(c, t, e) => {
                if self.eval_bool(c)? {
                    self.eval_real(t)
                } else {
                    self.eval_real(e)
                }
            }
            Term::Let { bindings, body } => {
                let substituted = self.substitute_let(bindings, body);
                self.eval_real(&substituted)
            }
            _ => None,
        }
    }

    /// Evaluate a term to a string value
    pub fn eval_string(&self, term: &Term) -> Option<String> {
        match term {
            Term::StringLiteral(s) => Some(s.clone()),
            Term::Variable(name) => {
                if let Some((params, body)) = self.defined_funs.get(name) {
                    if params.is_empty() {
                        return self.eval_string(&body);
                    }
                }
                match self.variables.get(name)?.value.as_ref()? {
                    TheoryValue::Str(s) => Some(s.clone()),
                    _ => None,
                }
            }
            Term::StrConcat(ts) => {
                let mut result = String::new();
                for t in ts {
                    result.push_str(&self.eval_string(t)?);
                }
                Some(result)
            }
            Term::StrAt(s, i) => {
                let ss = self.eval_string(s)?;
                let si = self.eval_int(i)? as usize;
                if si < ss.len() {
                    Some(ss.chars().nth(si)?.to_string())
                } else {
                    Some(String::new())
                }
            }
            Term::StrSubstr(s, i, l) => {
                let ss = self.eval_string(s)?;
                let si = self.eval_int(i)? as usize;
                let sl = self.eval_int(l)? as usize;
                if si > ss.len() {
                    return Some(String::new());
                }
                let end = (si + sl).min(ss.len());
                Some(ss[si..end].to_string())
            }
            Term::StrReplace(s, a, b) => {
                let ss = self.eval_string(s)?;
                let sa = self.eval_string(a)?;
                let sb = self.eval_string(b)?;
                Some(ss.replacen(&sa, &sb, 1))
            }
            Term::IntToStr(t) => {
                let v = self.eval_int(t)?;
                if v >= 0 {
                    Some(v.to_string())
                } else {
                    Some(String::new())
                }
            }
            Term::Ite(c, t, e) => {
                if self.eval_bool(c)? {
                    self.eval_string(t)
                } else {
                    self.eval_string(e)
                }
            }
            Term::Let { bindings, body } => {
                let substituted = self.substitute_let(bindings, body);
                self.eval_string(&substituted)
            }
            _ => None,
        }
    }

    /// Evaluate a term to a TheoryValue (any type)
    pub fn eval_value(&self, term: &Term) -> Option<TheoryValue> {
        if let Some(v) = self.eval_int(term) {
            return Some(TheoryValue::Int(v));
        }
        if let Some(v) = self.eval_real(term) {
            return Some(TheoryValue::Real(v));
        }
        if let Some(v) = self.eval_string(term) {
            return Some(TheoryValue::Str(v));
        }
        if let Some(v) = self.eval_bool(term) {
            return Some(TheoryValue::Bool(v));
        }
        None
    }

    /// Simple let substitution for evaluation
    fn substitute_let(&self, bindings: &[(String, Term)], body: &Term) -> Term {
        let mut result = body.clone();
        for (name, val) in bindings.iter().rev() {
            result = substitute_var(&result, name, val);
        }
        result
    }

    /// Get model value for a variable as formatted string
    pub fn get_model_value(&self, name: &str, sort: &Sort) -> Option<String> {
        let var = self.variables.get(name)?;
        let val = var.value.as_ref()?;
        match (sort, val) {
            (Sort::Int, TheoryValue::Int(n)) => {
                if *n < 0 {
                    Some(format!("(- {})", -n))
                } else {
                    Some(format!("{}", n))
                }
            }
            (Sort::Real, TheoryValue::Real(v)) => {
                if *v < 0.0 {
                    Some(format!("(- {})", format_real(-v)))
                } else {
                    Some(format_real(*v))
                }
            }
            (Sort::String, TheoryValue::Str(s)) => Some(format!("\"{}\"", s)),
            _ => None,
        }
    }
}

/// Euclidean integer division (SMT-LIB semantics)
fn euclidean_div(a: i64, b: i64) -> i64 {
    let d = a / b;
    let r = a % b;
    if r < 0 {
        if b > 0 { d - 1 } else { d + 1 }
    } else {
        d
    }
}

/// Euclidean modulo (SMT-LIB semantics)
fn euclidean_mod(a: i64, b: i64) -> i64 {
    let r = a % b;
    if r < 0 { r + b.abs() } else { r }
}

/// Substitute a variable name with a term in an expression
fn substitute_var(term: &Term, name: &str, replacement: &Term) -> Term {
    match term {
        Term::Variable(n) if n == name => replacement.clone(),
        Term::Variable(_) | Term::True | Term::False | Term::IntLiteral(_)
        | Term::RealLiteral(_, _) | Term::StringLiteral(_)
        | Term::BitVecLiteral { .. } => term.clone(),
        Term::Not(t) => Term::Not(Box::new(substitute_var(t, name, replacement))),
        Term::And(ts) => Term::And(ts.iter().map(|t| substitute_var(t, name, replacement)).collect()),
        Term::Or(ts) => Term::Or(ts.iter().map(|t| substitute_var(t, name, replacement)).collect()),
        Term::Xor(a, b) => Term::Xor(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Implies(a, b) => Term::Implies(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Eq(a, b) => Term::Eq(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Distinct(a, b) => Term::Distinct(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Ite(c, t, e) => Term::Ite(
            Box::new(substitute_var(c, name, replacement)),
            Box::new(substitute_var(t, name, replacement)),
            Box::new(substitute_var(e, name, replacement)),
        ),
        Term::Neg(t) => Term::Neg(Box::new(substitute_var(t, name, replacement))),
        Term::Add(ts) => Term::Add(ts.iter().map(|t| substitute_var(t, name, replacement)).collect()),
        Term::Sub(a, b) => Term::Sub(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Mul(ts) => Term::Mul(ts.iter().map(|t| substitute_var(t, name, replacement)).collect()),
        Term::Div(a, b) => Term::Div(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Mod(a, b) => Term::Mod(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Abs(t) => Term::Abs(Box::new(substitute_var(t, name, replacement))),
        Term::Lt(a, b) => Term::Lt(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Le(a, b) => Term::Le(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Gt(a, b) => Term::Gt(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Ge(a, b) => Term::Ge(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::ToReal(t) => Term::ToReal(Box::new(substitute_var(t, name, replacement))),
        Term::ToInt(t) => Term::ToInt(Box::new(substitute_var(t, name, replacement))),
        Term::IsInt(t) => Term::IsInt(Box::new(substitute_var(t, name, replacement))),
        Term::Divisible(n, t) => Term::Divisible(*n, Box::new(substitute_var(t, name, replacement))),
        Term::StrLen(t) => Term::StrLen(Box::new(substitute_var(t, name, replacement))),
        Term::StrConcat(ts) => Term::StrConcat(ts.iter().map(|t| substitute_var(t, name, replacement)).collect()),
        Term::StrAt(s, i) => Term::StrAt(
            Box::new(substitute_var(s, name, replacement)),
            Box::new(substitute_var(i, name, replacement)),
        ),
        Term::StrSubstr(s, i, l) => Term::StrSubstr(
            Box::new(substitute_var(s, name, replacement)),
            Box::new(substitute_var(i, name, replacement)),
            Box::new(substitute_var(l, name, replacement)),
        ),
        Term::StrContains(a, b) => Term::StrContains(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::StrIndexOf(s, t, i) => Term::StrIndexOf(
            Box::new(substitute_var(s, name, replacement)),
            Box::new(substitute_var(t, name, replacement)),
            Box::new(substitute_var(i, name, replacement)),
        ),
        Term::StrReplace(s, a, b) => Term::StrReplace(
            Box::new(substitute_var(s, name, replacement)),
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::StrPrefixOf(a, b) => Term::StrPrefixOf(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::StrSuffixOf(a, b) => Term::StrSuffixOf(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::StrToInt(t) => Term::StrToInt(Box::new(substitute_var(t, name, replacement))),
        Term::IntToStr(t) => Term::IntToStr(Box::new(substitute_var(t, name, replacement))),
        Term::StrLt(a, b) => Term::StrLt(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::StrLe(a, b) => Term::StrLe(
            Box::new(substitute_var(a, name, replacement)),
            Box::new(substitute_var(b, name, replacement)),
        ),
        Term::Let { bindings, body } => {
            // Don't substitute if shadowed
            let new_bindings: Vec<_> = bindings
                .iter()
                .map(|(n, v)| (n.clone(), substitute_var(v, name, replacement)))
                .collect();
            if bindings.iter().any(|(n, _)| n == name) {
                Term::Let { bindings: new_bindings, body: body.clone() }
            } else {
                Term::Let {
                    bindings: new_bindings,
                    body: Box::new(substitute_var(body, name, replacement)),
                }
            }
        }
        // BV terms - pass through unchanged since theory solver doesn't handle them
        other => other.clone(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatStatus {
    Sat,
    Unsat,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_eval() {
        let solver = TheorySolver::new();
        let term = Term::Add(vec![Term::IntLiteral(3), Term::IntLiteral(4)]);
        assert_eq!(solver.eval_int(&term), Some(7));
    }

    #[test]
    fn test_int_constraint() {
        let mut solver = TheorySolver::new();
        solver.declare_variable("x", &Sort::Int);
        solver.add_constraint(
            Term::Eq(
                Box::new(Term::Variable("x".into())),
                Box::new(Term::IntLiteral(5)),
            ),
            true,
        );
        assert_eq!(solver.check_sat(), SatStatus::Sat);
        let val = solver.variables.get("x").unwrap().value.clone();
        assert_eq!(val, Some(TheoryValue::Int(5)));
    }

    #[test]
    fn test_int_unsat() {
        let mut solver = TheorySolver::new();
        solver.declare_variable("x", &Sort::Int);
        solver.add_constraint(
            Term::Eq(
                Box::new(Term::Variable("x".into())),
                Box::new(Term::IntLiteral(5)),
            ),
            true,
        );
        solver.add_constraint(
            Term::Eq(
                Box::new(Term::Variable("x".into())),
                Box::new(Term::IntLiteral(3)),
            ),
            true,
        );
        assert_eq!(solver.check_sat(), SatStatus::Unsat);
    }

    #[test]
    fn test_string_eval() {
        let solver = TheorySolver::new();
        let term = Term::StrConcat(vec![
            Term::StringLiteral("hello".into()),
            Term::StringLiteral(" world".into()),
        ]);
        assert_eq!(solver.eval_string(&term), Some("hello world".into()));
    }

    #[test]
    fn test_string_len() {
        let solver = TheorySolver::new();
        let term = Term::StrLen(Box::new(Term::StringLiteral("hello".into())));
        assert_eq!(solver.eval_int(&term), Some(5));
    }

    #[test]
    fn test_string_constraint() {
        let mut solver = TheorySolver::new();
        solver.declare_variable("s", &Sort::String);
        solver.add_constraint(
            Term::Eq(
                Box::new(Term::Variable("s".into())),
                Box::new(Term::StringLiteral("hello".into())),
            ),
            true,
        );
        assert_eq!(solver.check_sat(), SatStatus::Sat);
        let val = solver.variables.get("s").unwrap().value.clone();
        assert_eq!(val, Some(TheoryValue::Str("hello".into())));
    }

    #[test]
    fn test_real_eval() {
        let solver = TheorySolver::new();
        let term = Term::Add(vec![
            Term::RealLiteral(3, 1),
            Term::RealLiteral(1, 2),
        ]);
        let v = solver.eval_real(&term).unwrap();
        assert!((v - 3.5).abs() < 1e-10);
    }

    #[test]
    fn test_int_comparison() {
        let mut solver = TheorySolver::new();
        solver.declare_variable("x", &Sort::Int);
        solver.add_constraint(
            Term::And(vec![
                Term::Gt(
                    Box::new(Term::Variable("x".into())),
                    Box::new(Term::IntLiteral(0)),
                ),
                Term::Lt(
                    Box::new(Term::Variable("x".into())),
                    Box::new(Term::IntLiteral(3)),
                ),
            ]),
            true,
        );
        assert_eq!(solver.check_sat(), SatStatus::Sat);
        match &solver.variables.get("x").unwrap().value {
            Some(TheoryValue::Int(v)) => assert!(*v > 0 && *v < 3),
            _ => panic!("expected int value"),
        }
    }

    #[test]
    fn test_euclidean_div_mod() {
        assert_eq!(euclidean_div(7, 3), 2);
        assert_eq!(euclidean_mod(7, 3), 1);
        assert_eq!(euclidean_div(-7, 3), -3);
        assert_eq!(euclidean_mod(-7, 3), 2);
    }

    #[test]
    fn test_str_contains() {
        let solver = TheorySolver::new();
        let term = Term::StrContains(
            Box::new(Term::StringLiteral("hello world".into())),
            Box::new(Term::StringLiteral("world".into())),
        );
        assert_eq!(solver.eval_bool(&term), Some(true));
    }

    #[test]
    fn test_str_substr() {
        let solver = TheorySolver::new();
        let term = Term::StrSubstr(
            Box::new(Term::StringLiteral("hello".into())),
            Box::new(Term::IntLiteral(1)),
            Box::new(Term::IntLiteral(3)),
        );
        assert_eq!(solver.eval_string(&term), Some("ell".into()));
    }

    #[test]
    fn test_int_mul() {
        let solver = TheorySolver::new();
        let term = Term::Mul(vec![Term::IntLiteral(3), Term::IntLiteral(7)]);
        assert_eq!(solver.eval_int(&term), Some(21));
    }
}

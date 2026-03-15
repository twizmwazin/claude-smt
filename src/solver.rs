//! SMT solver: processes SMT-LIB commands by translating assertions
//! into SAT via bit-blasting (for bitvectors) or direct encoding (for booleans),
//! and using theory solvers for Int, Real, and String.

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use crate::ast::{Command, Sort, Term};
use crate::bitvector::{BitBlaster, BitVec};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::sat::{Lit, SatResult, SatSolver};
use crate::theories::{SatStatus, TheorySolver, TheoryValue};

/// A typed value in the solver
#[derive(Debug, Clone)]
enum Value {
    Bool(Lit),
    BitVector(BitVec),
    Theory, // managed by TheorySolver
}

/// Stack frame for push/pop
struct Frame {
    var_snapshot: Vec<(String, Option<Value>)>,
    defined_snapshot: Vec<(String, Option<(Vec<(String, Sort)>, Term)>)>,
}

pub struct SmtSolver {
    sat: SatSolver,
    theory: TheorySolver,
    variables: HashMap<String, Value>,
    var_sorts: HashMap<String, Sort>,
    defined_funs: HashMap<String, (Vec<(String, Sort)>, Term)>,
    stack: Vec<Frame>,
    logic: Option<String>,
    produce_models: bool,
    theory_assertions: Vec<Term>,
}

impl SmtSolver {
    pub fn new() -> Self {
        SmtSolver {
            sat: SatSolver::new(),
            theory: TheorySolver::new(),
            variables: HashMap::new(),
            var_sorts: HashMap::new(),
            defined_funs: HashMap::new(),
            stack: Vec::new(),
            logic: None,
            produce_models: false,
            theory_assertions: Vec::new(),
        }
    }

    /// Run the solver in interactive mode, reading from stdin
    pub fn run_interactive(&mut self) {
        let stdin = io::stdin();
        let stdout = io::stdout();
        let mut out = stdout.lock();

        let mut input = String::new();
        for line in stdin.lock().lines() {
            match line {
                Ok(l) => {
                    input.push_str(&l);
                    input.push('\n');

                    if Self::parens_balanced(&input) {
                        match self.process_input(&input) {
                            Ok(responses) => {
                                for r in responses {
                                    writeln!(out, "{}", r).ok();
                                }
                                out.flush().ok();
                            }
                            Err(e) => {
                                writeln!(out, "(error \"{}\")", e).ok();
                                out.flush().ok();
                            }
                        }
                        input.clear();
                    }
                }
                Err(_) => break,
            }
        }
    }

    fn parens_balanced(s: &str) -> bool {
        let mut depth = 0i32;
        let mut in_string = false;
        for ch in s.chars() {
            if in_string {
                if ch == '"' {
                    in_string = false;
                }
                continue;
            }
            match ch {
                '"' => in_string = true,
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
        }
        depth <= 0 && !in_string
    }

    /// Process a string of SMT-LIB input and return responses
    pub fn process_input(&mut self, input: &str) -> Result<Vec<String>, String> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().map_err(|e| e.to_string())?;
        if tokens.is_empty() {
            return Ok(vec![]);
        }
        let mut parser = Parser::new(tokens);
        let commands = parser.parse_commands().map_err(|e| e.to_string())?;

        let mut responses = Vec::new();
        for cmd in commands {
            match self.execute_command(cmd) {
                Ok(Some(resp)) => responses.push(resp),
                Ok(None) => {}
                Err(e) => responses.push(format!("(error \"{}\")", e)),
            }
        }
        Ok(responses)
    }

    /// Determine if a term involves theory sorts (Int/Real/String)
    fn is_theory_term(&self, term: &Term) -> bool {
        match self.infer_sort(term) {
            Some(Sort::Int) | Some(Sort::Real) | Some(Sort::String) => true,
            _ => self.term_uses_theory(term),
        }
    }

    fn term_uses_theory(&self, term: &Term) -> bool {
        match term {
            Term::IntLiteral(_) | Term::RealLiteral(_, _) | Term::StringLiteral(_) => true,
            Term::Neg(_) | Term::Add(_) | Term::Sub(_, _) | Term::Mul(_) | Term::Div(_, _)
            | Term::Mod(_, _) | Term::Abs(_) | Term::Lt(_, _) | Term::Le(_, _)
            | Term::Gt(_, _) | Term::Ge(_, _) | Term::ToReal(_) | Term::ToInt(_)
            | Term::IsInt(_) | Term::Divisible(_, _) => true,
            Term::StrLen(_) | Term::StrConcat(_) | Term::StrAt(_, _) | Term::StrSubstr(_, _, _)
            | Term::StrContains(_, _) | Term::StrIndexOf(_, _, _) | Term::StrReplace(_, _, _)
            | Term::StrPrefixOf(_, _) | Term::StrSuffixOf(_, _) | Term::StrToInt(_)
            | Term::IntToStr(_) | Term::StrLt(_, _) | Term::StrLe(_, _) => true,
            Term::Variable(name) => {
                matches!(
                    self.var_sorts.get(name),
                    Some(Sort::Int) | Some(Sort::Real) | Some(Sort::String)
                )
            }
            Term::Not(t) => self.term_uses_theory(t),
            Term::And(ts) | Term::Or(ts) => ts.iter().any(|t| self.term_uses_theory(t)),
            Term::Xor(a, b) | Term::Implies(a, b) | Term::Eq(a, b) | Term::Distinct(a, b) => {
                self.term_uses_theory(a) || self.term_uses_theory(b)
            }
            Term::Ite(c, t, e) => {
                self.term_uses_theory(c) || self.term_uses_theory(t) || self.term_uses_theory(e)
            }
            Term::Let { bindings, body } => {
                bindings.iter().any(|(_, v)| self.term_uses_theory(v)) || self.term_uses_theory(body)
            }
            _ => false,
        }
    }

    fn execute_command(&mut self, cmd: Command) -> Result<Option<String>, String> {
        match cmd {
            Command::SetLogic(logic) => {
                self.logic = Some(logic);
                Ok(None)
            }
            Command::SetOption(key, val) => {
                if key == "produce-models" && val == "true" {
                    self.produce_models = true;
                }
                Ok(None)
            }
            Command::SetInfo(_, _) => Ok(None),
            Command::DeclareConst(name, sort) => {
                self.declare_variable(&name, &sort);
                Ok(None)
            }
            Command::DeclareFun(name, arg_sorts, ret_sort) => {
                if !arg_sorts.is_empty() {
                    return Err("uninterpreted functions not supported".into());
                }
                self.declare_variable(&name, &ret_sort);
                Ok(None)
            }
            Command::DefineFun(name, params, _sort, body) => {
                self.defined_funs.insert(name.clone(), (params.clone(), body.clone()));
                self.theory.define_fun(name, params, body);
                Ok(None)
            }
            Command::Assert(term) => {
                if self.is_theory_term(&term) {
                    self.theory_assertions.push(term.clone());
                    self.theory.add_constraint(term, true);
                } else {
                    let lit = self.encode_bool_term(&term)?;
                    self.sat.add_clause(vec![lit]);
                }
                Ok(None)
            }
            Command::CheckSat => {
                let has_theory = !self.theory_assertions.is_empty()
                    || self.var_sorts.values().any(|s| {
                        matches!(s, Sort::Int | Sort::Real | Sort::String)
                    });

                if has_theory {
                    // Check theory constraints
                    let sat_result = self.sat.solve();
                    let theory_result = self.theory.check_sat();

                    match (sat_result, theory_result) {
                        (SatResult::Sat, SatStatus::Sat) | (SatResult::Sat, _)
                            if self.theory_assertions.is_empty() =>
                        {
                            Ok(Some("sat".into()))
                        }
                        (_, SatStatus::Sat) if !has_bool_bv_vars(&self.var_sorts) => {
                            Ok(Some("sat".into()))
                        }
                        (SatResult::Sat, SatStatus::Sat) => Ok(Some("sat".into())),
                        (SatResult::Unsat, _) => Ok(Some("unsat".into())),
                        (_, SatStatus::Unsat) => Ok(Some("unsat".into())),
                        _ => Ok(Some("unknown".into())),
                    }
                } else {
                    let result = self.sat.solve();
                    Ok(Some(match result {
                        SatResult::Sat => "sat".to_string(),
                        SatResult::Unsat => "unsat".to_string(),
                        SatResult::Unknown => "unknown".to_string(),
                    }))
                }
            }
            Command::GetModel => {
                let mut model = String::from("(\n");
                let mut sorted_vars: Vec<_> = self.var_sorts.iter().collect();
                sorted_vars.sort_by_key(|(name, _)| (*name).clone());
                for (name, sort) in &sorted_vars {
                    match sort {
                        Sort::Bool => {
                            if let Some(Value::Bool(lit)) = self.variables.get(*name) {
                                let v = lit.unsigned_abs();
                                let val = match self.sat.model_value(v) {
                                    Some(b) => {
                                        let actual = if *lit > 0 { b } else { !b };
                                        if actual { "true" } else { "false" }
                                    }
                                    None => "true",
                                };
                                model.push_str(&format!(
                                    "  (define-fun {} () Bool {})\n",
                                    name, val
                                ));
                            }
                        }
                        Sort::BitVec(w) => {
                            if let Some(Value::BitVector(bv)) = self.variables.get(*name) {
                                let val = bv.get_value(&self.sat).unwrap_or(0);
                                model.push_str(&format!(
                                    "  (define-fun {} () (_ BitVec {}) (_ bv{} {}))\n",
                                    name, w, val, w
                                ));
                            }
                        }
                        Sort::Int => {
                            if let Some(val_str) = self.theory.get_model_value(name, sort) {
                                model.push_str(&format!(
                                    "  (define-fun {} () Int {})\n",
                                    name, val_str
                                ));
                            }
                        }
                        Sort::Real => {
                            if let Some(val_str) = self.theory.get_model_value(name, sort) {
                                model.push_str(&format!(
                                    "  (define-fun {} () Real {})\n",
                                    name, val_str
                                ));
                            }
                        }
                        Sort::String => {
                            if let Some(val_str) = self.theory.get_model_value(name, sort) {
                                model.push_str(&format!(
                                    "  (define-fun {} () String {})\n",
                                    name, val_str
                                ));
                            }
                        }
                    }
                }
                model.push(')');
                Ok(Some(model))
            }
            Command::GetValue(terms) => {
                let mut result = String::from("(");
                for (i, term) in terms.iter().enumerate() {
                    if i > 0 {
                        result.push(' ');
                    }
                    let val = self.eval_term(term)?;
                    result.push_str(&format!("({} {})", term, val));
                }
                result.push(')');
                Ok(Some(result))
            }
            Command::Push(n) => {
                for _ in 0..n {
                    self.stack.push(Frame {
                        var_snapshot: Vec::new(),
                        defined_snapshot: Vec::new(),
                    });
                }
                Ok(None)
            }
            Command::Pop(n) => {
                for _ in 0..n {
                    if let Some(frame) = self.stack.pop() {
                        for (name, old_val) in frame.var_snapshot.into_iter().rev() {
                            match old_val {
                                Some(v) => { self.variables.insert(name, v); }
                                None => { self.variables.remove(&name); }
                            }
                        }
                        for (name, old_def) in frame.defined_snapshot.into_iter().rev() {
                            match old_def {
                                Some(d) => { self.defined_funs.insert(name, d); }
                                None => { self.defined_funs.remove(&name); }
                            }
                        }
                    }
                }
                Ok(None)
            }
            Command::Reset => {
                *self = SmtSolver::new();
                Ok(None)
            }
            Command::ResetAssertions => {
                self.sat = SatSolver::new();
                self.theory.reset();
                self.variables.clear();
                self.var_sorts.clear();
                self.stack.clear();
                self.theory_assertions.clear();
                Ok(None)
            }
            Command::Exit => Ok(None),
            Command::Echo(msg) => Ok(Some(format!("\"{}\"", msg))),
        }
    }

    fn declare_variable(&mut self, name: &str, sort: &Sort) {
        let value = match sort {
            Sort::Bool => {
                let v = self.sat.new_var();
                Value::Bool(v as Lit)
            }
            Sort::BitVec(w) => {
                let bv = BitVec::new_variable(&mut self.sat, *w);
                Value::BitVector(bv)
            }
            Sort::Int | Sort::Real | Sort::String => {
                self.theory.declare_variable(name, sort);
                Value::Theory
            }
        };
        self.variables.insert(name.to_string(), value);
        self.var_sorts.insert(name.to_string(), sort.clone());
    }

    /// Encode a term that should evaluate to Bool, returning a SAT literal
    fn encode_bool_term(&mut self, term: &Term) -> Result<Lit, String> {
        match term {
            Term::True => {
                let v = self.sat.new_var();
                let lit = v as Lit;
                self.sat.add_clause(vec![lit]);
                Ok(lit)
            }
            Term::False => {
                let v = self.sat.new_var();
                let lit = v as Lit;
                self.sat.add_clause(vec![-lit]);
                Ok(lit)
            }
            Term::Variable(name) => {
                if let Some((params, body)) = self.defined_funs.get(name).cloned() {
                    if params.is_empty() {
                        return self.encode_bool_term(&body);
                    }
                }
                match self.variables.get(name) {
                    Some(Value::Bool(lit)) => Ok(*lit),
                    Some(Value::BitVector(_)) => {
                        Err(format!("expected Bool, got BitVec for '{}'", name))
                    }
                    Some(Value::Theory) => {
                        Err(format!("cannot encode theory variable '{}' as SAT literal", name))
                    }
                    None => Err(format!("undeclared variable: '{}'", name)),
                }
            }
            Term::Not(t) => {
                let lit = self.encode_bool_term(t)?;
                Ok(-lit)
            }
            Term::And(terms) => {
                if terms.is_empty() {
                    let v = self.sat.new_var();
                    let lit = v as Lit;
                    self.sat.add_clause(vec![lit]);
                    return Ok(lit);
                }
                let lits: Vec<Lit> = terms
                    .iter()
                    .map(|t| self.encode_bool_term(t))
                    .collect::<Result<_, _>>()?;
                if lits.len() == 1 {
                    return Ok(lits[0]);
                }
                let r = self.sat.new_var() as Lit;
                for &l in &lits {
                    self.sat.add_clause(vec![-r, l]);
                }
                let mut clause: Vec<Lit> = lits.iter().map(|&l| -l).collect();
                clause.push(r);
                self.sat.add_clause(clause);
                Ok(r)
            }
            Term::Or(terms) => {
                if terms.is_empty() {
                    let v = self.sat.new_var();
                    let lit = v as Lit;
                    self.sat.add_clause(vec![-lit]);
                    return Ok(lit);
                }
                let lits: Vec<Lit> = terms
                    .iter()
                    .map(|t| self.encode_bool_term(t))
                    .collect::<Result<_, _>>()?;
                if lits.len() == 1 {
                    return Ok(lits[0]);
                }
                let r = self.sat.new_var() as Lit;
                let mut clause = vec![-r];
                clause.extend_from_slice(&lits);
                self.sat.add_clause(clause);
                for &l in &lits {
                    self.sat.add_clause(vec![-l, r]);
                }
                Ok(r)
            }
            Term::Xor(a, b) => {
                let la = self.encode_bool_term(a)?;
                let lb = self.encode_bool_term(b)?;
                let r = self.sat.new_var() as Lit;
                self.sat.add_clause(vec![-r, -la, -lb]);
                self.sat.add_clause(vec![-r, la, lb]);
                self.sat.add_clause(vec![r, -la, lb]);
                self.sat.add_clause(vec![r, la, -lb]);
                Ok(r)
            }
            Term::Implies(a, b) => {
                let la = self.encode_bool_term(a)?;
                let lb = self.encode_bool_term(b)?;
                let r = self.sat.new_var() as Lit;
                self.sat.add_clause(vec![-r, -la, lb]);
                self.sat.add_clause(vec![la, r]);
                self.sat.add_clause(vec![-lb, r]);
                Ok(r)
            }
            Term::Ite(cond, then_t, else_t) => {
                let then_sort = self.infer_sort(then_t);
                if then_sort == Some(Sort::Bool) || self.infer_sort(cond) == Some(Sort::Bool) {
                    if let (Ok(lt), Ok(le)) = (
                        self.encode_bool_term(then_t),
                        self.encode_bool_term(else_t),
                    ) {
                        let lc = self.encode_bool_term(cond)?;
                        let r = self.sat.new_var() as Lit;
                        self.sat.add_clause(vec![-lc, -r, lt]);
                        self.sat.add_clause(vec![-lc, r, -lt]);
                        self.sat.add_clause(vec![lc, -r, le]);
                        self.sat.add_clause(vec![lc, r, -le]);
                        return Ok(r);
                    }
                }
                Err("ite with non-boolean result used in boolean context".into())
            }
            Term::Eq(a, b) => {
                let sort_a = self.infer_sort(a);
                let sort_b = self.infer_sort(b);
                match (&sort_a, &sort_b) {
                    (Some(Sort::Bool), _) | (_, Some(Sort::Bool)) => {
                        let la = self.encode_bool_term(a)?;
                        let lb = self.encode_bool_term(b)?;
                        let r = self.sat.new_var() as Lit;
                        self.sat.add_clause(vec![-r, -la, lb]);
                        self.sat.add_clause(vec![-r, la, -lb]);
                        self.sat.add_clause(vec![r, -la, -lb]);
                        self.sat.add_clause(vec![r, la, lb]);
                        Ok(r)
                    }
                    (Some(Sort::Int), _) | (_, Some(Sort::Int))
                    | (Some(Sort::Real), _) | (_, Some(Sort::Real))
                    | (Some(Sort::String), _) | (_, Some(Sort::String)) => {
                        Err("theory equality should be handled by theory solver".into())
                    }
                    _ => {
                        let bva = self.encode_bv_term(a)?;
                        let bvb = self.encode_bv_term(b)?;
                        let mut bb = BitBlaster::new(&mut self.sat);
                        Ok(bb.eq(&bva, &bvb))
                    }
                }
            }
            Term::Distinct(a, b) => {
                let eq_lit = self.encode_bool_term(&Term::Eq(
                    Box::new(a.as_ref().clone()),
                    Box::new(b.as_ref().clone()),
                ))?;
                Ok(-eq_lit)
            }

            // BV comparison operations return Bool
            Term::BvUlt(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvult_lit(&bva, &bvb))
            }
            Term::BvUle(a, b) => {
                let bvb = self.encode_bv_term(b)?;
                let bva = self.encode_bv_term(a)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                let b_lt_a = bb.bvult_lit(&bvb, &bva);
                Ok(-b_lt_a)
            }
            Term::BvUgt(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvult_lit(&bvb, &bva))
            }
            Term::BvUge(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                let a_lt_b = bb.bvult_lit(&bva, &bvb);
                Ok(-a_lt_b)
            }
            Term::BvSlt(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvslt_lit(&bva, &bvb))
            }
            Term::BvSle(a, b) => {
                let bvb = self.encode_bv_term(b)?;
                let bva = self.encode_bv_term(a)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                let b_lt_a = bb.bvslt_lit(&bvb, &bva);
                Ok(-b_lt_a)
            }
            Term::BvSgt(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvslt_lit(&bvb, &bva))
            }
            Term::BvSge(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                let a_lt_b = bb.bvslt_lit(&bva, &bvb);
                Ok(-a_lt_b)
            }

            Term::Let { bindings, body } => {
                let mut saved = Vec::new();
                for (name, val_term) in bindings {
                    let old = self.variables.get(name).cloned();
                    saved.push((name.clone(), old));

                    let sort = self.infer_sort(val_term);
                    match sort {
                        Some(Sort::Bool) | None => {
                            match self.encode_bool_term(val_term) {
                                Ok(lit) => {
                                    self.variables.insert(name.clone(), Value::Bool(lit));
                                    self.var_sorts.insert(name.clone(), Sort::Bool);
                                }
                                Err(_) => {
                                    let bv = self.encode_bv_term(val_term)?;
                                    let w = bv.width();
                                    self.variables.insert(name.clone(), Value::BitVector(bv));
                                    self.var_sorts.insert(name.clone(), Sort::BitVec(w));
                                }
                            }
                        }
                        Some(Sort::BitVec(_)) => {
                            let bv = self.encode_bv_term(val_term)?;
                            let w = bv.width();
                            self.variables.insert(name.clone(), Value::BitVector(bv));
                            self.var_sorts.insert(name.clone(), Sort::BitVec(w));
                        }
                        Some(Sort::Int) | Some(Sort::Real) | Some(Sort::String) => {
                            self.variables.insert(name.clone(), Value::Theory);
                            self.var_sorts.insert(name.clone(), sort.unwrap());
                        }
                    }
                }

                let result = self.encode_bool_term(body);

                for (name, old) in saved.into_iter().rev() {
                    match old {
                        Some(v) => { self.variables.insert(name, v); }
                        None => { self.variables.remove(&name); }
                    }
                }
                result
            }

            _ => Err(format!("term not supported in boolean context: {:?}", term)),
        }
    }

    /// Encode a term that should evaluate to a bitvector
    fn encode_bv_term(&mut self, term: &Term) -> Result<BitVec, String> {
        match term {
            Term::BitVecLiteral { value, width } => {
                if *width == 0 {
                    return Err("bitvector literal with unknown width".into());
                }
                Ok(BitVec::from_constant(&mut self.sat, *value, *width))
            }
            Term::Variable(name) => {
                if let Some((params, body)) = self.defined_funs.get(name).cloned() {
                    if params.is_empty() {
                        return self.encode_bv_term(&body);
                    }
                }
                match self.variables.get(name) {
                    Some(Value::BitVector(bv)) => Ok(bv.clone()),
                    Some(Value::Bool(_)) => {
                        Err(format!("expected BitVec, got Bool for '{}'", name))
                    }
                    Some(Value::Theory) => {
                        Err(format!("expected BitVec, got theory sort for '{}'", name))
                    }
                    None => Err(format!("undeclared variable: '{}'", name)),
                }
            }
            Term::BvNot(t) => {
                let bv = self.encode_bv_term(t)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvnot(&bv))
            }
            Term::BvAnd(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvand(&bva, &bvb))
            }
            Term::BvOr(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvor(&bva, &bvb))
            }
            Term::BvXor(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvxor(&bva, &bvb))
            }
            Term::BvNeg(t) => {
                let bv = self.encode_bv_term(t)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvneg(&bv))
            }
            Term::BvAdd(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvadd(&bva, &bvb))
            }
            Term::BvSub(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvsub(&bva, &bvb))
            }
            Term::BvMul(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvmul(&bva, &bvb))
            }
            Term::BvUdiv(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvudiv(&bva, &bvb))
            }
            Term::BvUrem(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvurem(&bva, &bvb))
            }
            Term::BvSdiv(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvsdiv(&bva, &bvb))
            }
            Term::BvSrem(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvsrem(&bva, &bvb))
            }
            Term::BvShl(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvshl(&bva, &bvb))
            }
            Term::BvLshr(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvlshr(&bva, &bvb))
            }
            Term::BvAshr(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.bvashr(&bva, &bvb))
            }
            Term::Concat(a, b) => {
                let bva = self.encode_bv_term(a)?;
                let bvb = self.encode_bv_term(b)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.concat(&bva, &bvb))
            }
            Term::Extract { high, low, term } => {
                let bv = self.encode_bv_term(term)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.extract(*high, *low, &bv))
            }
            Term::ZeroExtend(n, t) => {
                let bv = self.encode_bv_term(t)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.zero_extend(*n, &bv))
            }
            Term::SignExtend(n, t) => {
                let bv = self.encode_bv_term(t)?;
                let mut bb = BitBlaster::new(&mut self.sat);
                Ok(bb.sign_extend(*n, &bv))
            }
            Term::Ite(cond, then_t, else_t) => {
                let cond_lit = self.encode_bool_term(cond)?;
                let then_bv = self.encode_bv_term(then_t)?;
                let else_bv = self.encode_bv_term(else_t)?;
                assert_eq!(then_bv.width(), else_bv.width());
                let w = then_bv.width() as usize;
                let mut bits = Vec::with_capacity(w);
                for i in 0..w {
                    let r = self.sat.new_var() as Lit;
                    self.sat.add_clause(vec![-cond_lit, -r, then_bv.bits[i]]);
                    self.sat.add_clause(vec![-cond_lit, r, -then_bv.bits[i]]);
                    self.sat.add_clause(vec![cond_lit, -r, else_bv.bits[i]]);
                    self.sat.add_clause(vec![cond_lit, r, -else_bv.bits[i]]);
                    bits.push(r);
                }
                Ok(BitVec { bits })
            }
            Term::Let { bindings, body } => {
                let mut saved = Vec::new();
                for (name, val_term) in bindings {
                    let old = self.variables.get(name).cloned();
                    saved.push((name.clone(), old));

                    let sort = self.infer_sort(val_term);
                    match sort {
                        Some(Sort::BitVec(_)) => {
                            let bv = self.encode_bv_term(val_term)?;
                            let w = bv.width();
                            self.variables.insert(name.clone(), Value::BitVector(bv));
                            self.var_sorts.insert(name.clone(), Sort::BitVec(w));
                        }
                        _ => {
                            match self.encode_bv_term(val_term) {
                                Ok(bv) => {
                                    let w = bv.width();
                                    self.variables.insert(name.clone(), Value::BitVector(bv));
                                    self.var_sorts.insert(name.clone(), Sort::BitVec(w));
                                }
                                Err(_) => {
                                    let lit = self.encode_bool_term(val_term)?;
                                    self.variables.insert(name.clone(), Value::Bool(lit));
                                    self.var_sorts.insert(name.clone(), Sort::Bool);
                                }
                            }
                        }
                    }
                }

                let result = self.encode_bv_term(body);

                for (name, old) in saved.into_iter().rev() {
                    match old {
                        Some(v) => { self.variables.insert(name, v); }
                        None => { self.variables.remove(&name); }
                    }
                }

                result
            }
            _ => Err(format!("term not supported in bitvector context: {:?}", term)),
        }
    }

    /// Try to infer the sort of a term
    fn infer_sort(&self, term: &Term) -> Option<Sort> {
        match term {
            Term::True | Term::False => Some(Sort::Bool),
            Term::BitVecLiteral { width, .. } => {
                if *width > 0 {
                    Some(Sort::BitVec(*width))
                } else {
                    None
                }
            }
            Term::IntLiteral(_) => Some(Sort::Int),
            Term::RealLiteral(_, _) => Some(Sort::Real),
            Term::StringLiteral(_) => Some(Sort::String),
            Term::Variable(name) => self.var_sorts.get(name).cloned(),
            Term::Not(_) | Term::And(_) | Term::Or(_) | Term::Xor(_, _)
            | Term::Implies(_, _) => Some(Sort::Bool),
            Term::Eq(_, _) | Term::Distinct(_, _) => Some(Sort::Bool),
            Term::BvUlt(_, _) | Term::BvUle(_, _) | Term::BvUgt(_, _) | Term::BvUge(_, _)
            | Term::BvSlt(_, _) | Term::BvSle(_, _) | Term::BvSgt(_, _) | Term::BvSge(_, _) => {
                Some(Sort::Bool)
            }
            Term::Lt(_, _) | Term::Le(_, _) | Term::Gt(_, _) | Term::Ge(_, _) => Some(Sort::Bool),
            Term::IsInt(_) | Term::Divisible(_, _) => Some(Sort::Bool),
            Term::StrContains(_, _) | Term::StrPrefixOf(_, _) | Term::StrSuffixOf(_, _)
            | Term::StrLt(_, _) | Term::StrLe(_, _) => Some(Sort::Bool),
            Term::BvNot(t) | Term::BvNeg(t) => self.infer_sort(t),
            Term::BvAnd(a, _) | Term::BvOr(a, _) | Term::BvXor(a, _)
            | Term::BvAdd(a, _) | Term::BvSub(a, _) | Term::BvMul(a, _)
            | Term::BvUdiv(a, _) | Term::BvUrem(a, _) | Term::BvSdiv(a, _)
            | Term::BvSrem(a, _) | Term::BvShl(a, _) | Term::BvLshr(a, _)
            | Term::BvAshr(a, _) => self.infer_sort(a),
            Term::Extract { high, low, .. } => Some(Sort::BitVec(high - low + 1)),
            Term::Concat(a, b) => {
                match (self.infer_sort(a), self.infer_sort(b)) {
                    (Some(Sort::BitVec(wa)), Some(Sort::BitVec(wb))) => {
                        Some(Sort::BitVec(wa + wb))
                    }
                    _ => None,
                }
            }
            Term::ZeroExtend(n, t) | Term::SignExtend(n, t) => {
                self.infer_sort(t).map(|s| match s {
                    Sort::BitVec(w) => Sort::BitVec(w + n),
                    other => other,
                })
            }
            Term::Neg(t) | Term::Abs(t) => self.infer_sort(t),
            Term::Add(ts) | Term::Mul(ts) => {
                for t in ts {
                    if let Some(s) = self.infer_sort(t) {
                        return Some(s);
                    }
                }
                None
            }
            Term::Sub(a, _) | Term::Div(a, _) | Term::Mod(a, _) => self.infer_sort(a),
            Term::ToReal(_) => Some(Sort::Real),
            Term::ToInt(_) => Some(Sort::Int),
            Term::StrLen(_) | Term::StrToInt(_) | Term::StrIndexOf(_, _, _) => Some(Sort::Int),
            Term::StrConcat(_) | Term::StrAt(_, _) | Term::StrSubstr(_, _, _)
            | Term::StrReplace(_, _, _) | Term::IntToStr(_) => Some(Sort::String),
            Term::Ite(_, t, _) => self.infer_sort(t),
            Term::Let { body, .. } => self.infer_sort(body),
        }
    }

    fn eval_term(&self, term: &Term) -> Result<String, String> {
        match term {
            Term::Variable(name) => match self.variables.get(name) {
                Some(Value::Bool(lit)) => {
                    let v = lit.unsigned_abs();
                    match self.sat.model_value(v) {
                        Some(b) => {
                            let actual = if *lit > 0 { b } else { !b };
                            Ok(if actual { "true".into() } else { "false".into() })
                        }
                        None => Ok("true".into()),
                    }
                }
                Some(Value::BitVector(bv)) => {
                    let val = bv.get_value(&self.sat).unwrap_or(0);
                    let w = bv.width();
                    Ok(format!("(_ bv{} {})", val, w))
                }
                Some(Value::Theory) => {
                    let sort = self.var_sorts.get(name).ok_or("unknown sort")?;
                    self.theory
                        .get_model_value(name, sort)
                        .ok_or_else(|| format!("no value for theory variable: {}", name))
                }
                None => Err(format!("unknown variable: {}", name)),
            },
            _ => {
                // Try theory evaluation
                if let Some(val) = self.theory.eval_value(term) {
                    Ok(val.to_string())
                } else {
                    Err("get-value only supports variables and theory terms".into())
                }
            }
        }
    }
}

fn has_bool_bv_vars(var_sorts: &HashMap<String, Sort>) -> bool {
    var_sorts.values().any(|s| matches!(s, Sort::Bool | Sort::BitVec(_)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(input: &str) -> Vec<String> {
        let mut solver = SmtSolver::new();
        solver.process_input(input).unwrap()
    }

    // === Existing Bool tests ===

    #[test]
    fn test_bool_sat() {
        let result = check(
            "(declare-const x Bool)
             (declare-const y Bool)
             (assert (or x y))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_bool_unsat() {
        let result = check(
            "(declare-const x Bool)
             (assert x)
             (assert (not x))
             (check-sat)",
        );
        assert_eq!(result, vec!["unsat"]);
    }

    // === Existing BV tests ===

    #[test]
    fn test_bv_sat() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (declare-const y (_ BitVec 8))
             (assert (= (bvadd x y) #xFF))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_bv_unsat() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 4))
             (assert (= x #xF))
             (assert (= x #x0))
             (check-sat)",
        );
        assert_eq!(result, vec!["unsat"]);
    }

    #[test]
    fn test_bv_arithmetic() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (assert (= x #x05))
             (assert (= (bvadd x x) #x0A))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_bool_implies() {
        let result = check(
            "(declare-const a Bool)
             (declare-const b Bool)
             (assert (=> a b))
             (assert a)
             (assert (not b))
             (check-sat)",
        );
        assert_eq!(result, vec!["unsat"]);
    }

    #[test]
    fn test_bv_comparison() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (assert (bvult x #x05))
             (assert (bvugt x #x02))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_bv_shift() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (assert (= x #x01))
             (assert (= (bvshl x #x02) #x04))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_bv_extract() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (assert (= x #xAB))
             (assert (= ((_ extract 3 0) x) #xB))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_bv_concat() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 4))
             (declare-const y (_ BitVec 4))
             (assert (= x #xA))
             (assert (= y #xB))
             (assert (= (concat x y) #xAB))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_get_model() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (assert (= x #x42))
             (check-sat)
             (get-model)",
        );
        assert_eq!(result[0], "sat");
        assert!(result[1].contains("define-fun x"));
        assert!(result[1].contains("bv66 8"));
    }

    #[test]
    fn test_echo() {
        let result = check("(echo \"hello world\")");
        assert_eq!(result, vec!["\"hello world\""]);
    }

    #[test]
    fn test_xor() {
        let result = check(
            "(declare-const a Bool)
             (declare-const b Bool)
             (assert (xor a b))
             (assert a)
             (assert b)
             (check-sat)",
        );
        assert_eq!(result, vec!["unsat"]);
    }

    #[test]
    fn test_distinct() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (declare-const y (_ BitVec 8))
             (assert (distinct x y))
             (assert (= x #x05))
             (assert (= y #x05))
             (check-sat)",
        );
        assert_eq!(result, vec!["unsat"]);
    }

    #[test]
    fn test_bv_mul() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (declare-const y (_ BitVec 8))
             (assert (= x #x03))
             (assert (= y #x07))
             (assert (= (bvmul x y) #x15))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_define_fun() {
        let result = check(
            "(declare-const x Bool)
             (define-fun my_not ((a Bool)) Bool (not a))
             (assert x)
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_sign_extend() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 4))
             (assert (= x #xF))
             (assert (= ((_ sign_extend 4) x) #xFF))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_zero_extend() {
        let result = check(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 4))
             (assert (= x #xF))
             (assert (= ((_ zero_extend 4) x) #x0F))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    // === New Int tests ===

    #[test]
    fn test_int_sat() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 5))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_int_unsat() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 5))
             (assert (= x 3))
             (check-sat)",
        );
        assert_eq!(result, vec!["unsat"]);
    }

    #[test]
    fn test_int_arithmetic() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= (+ x 3) 10))
             (check-sat)
             (get-model)",
        );
        assert_eq!(result[0], "sat");
        assert!(result[1].contains("define-fun x () Int 7"));
    }

    #[test]
    fn test_int_comparison() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (> x 0))
             (assert (< x 3))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_int_mul() {
        let result = check(
            "(set-logic QF_NIA)
             (declare-const x Int)
             (assert (= (* x 3) 21))
             (check-sat)
             (get-model)",
        );
        assert_eq!(result[0], "sat");
        assert!(result[1].contains("define-fun x () Int 7"));
    }

    #[test]
    fn test_int_mod() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 7))
             (assert (= (mod x 3) 1))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_int_abs() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x (- 5)))
             (assert (= (abs x) 5))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_int_distinct() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (assert (distinct x y))
             (assert (= x 5))
             (assert (= y 5))
             (check-sat)",
        );
        assert_eq!(result, vec!["unsat"]);
    }

    // === New Real tests ===

    #[test]
    fn test_real_sat() {
        let result = check(
            "(set-logic QF_LRA)
             (declare-const x Real)
             (assert (= x 3.0))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_real_arithmetic() {
        let result = check(
            "(set-logic QF_LRA)
             (declare-const x Real)
             (assert (= (+ x 1.0) 4.0))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_real_comparison() {
        let result = check(
            "(set-logic QF_LRA)
             (declare-const x Real)
             (assert (> x 0.0))
             (assert (< x 2.0))
             (check-sat)",
        );
        assert_eq!(result, vec!["sat"]);
    }

    // === New String tests ===

    #[test]
    fn test_string_sat() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_string_unsat() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello"))
             (assert (= s "world"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["unsat"]);
    }

    #[test]
    fn test_string_len() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello"))
             (assert (= (str.len s) 5))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_string_concat() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello"))
             (assert (= (str.++ s " world") "hello world"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_string_contains() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello world"))
             (assert (str.contains s "world"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_string_contains_unsat() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello"))
             (assert (str.contains s "world"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["unsat"]);
    }

    #[test]
    fn test_string_prefix() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello world"))
             (assert (str.prefixof "hello" s))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_string_model() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "test"))
             (check-sat)
             (get-model)"#,
        );
        assert_eq!(result[0], "sat");
        assert!(result[1].contains("define-fun s () String \"test\""));
    }

    #[test]
    fn test_int_model() {
        let result = check(
            "(set-logic QF_LIA)
             (declare-const x Int)
             (assert (= x 42))
             (check-sat)
             (get-model)",
        );
        assert_eq!(result[0], "sat");
        assert!(result[1].contains("define-fun x () Int 42"));
    }

    #[test]
    fn test_string_substr() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello"))
             (assert (= (str.substr s 1 3) "ell"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_str_to_int() {
        let result = check(
            r#"(set-logic QF_S)
             (assert (= (str.to_int "42") 42))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_int_to_str() {
        let result = check(
            r#"(set-logic QF_S)
             (assert (= (str.from_int 42) "42"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }

    #[test]
    fn test_string_replace() {
        let result = check(
            r#"(set-logic QF_S)
             (declare-const s String)
             (assert (= s "hello world"))
             (assert (= (str.replace s "world" "rust") "hello rust"))
             (check-sat)"#,
        );
        assert_eq!(result, vec!["sat"]);
    }
}

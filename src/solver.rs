//! SMT solver: processes SMT-LIB commands by translating assertions
//! into SAT via bit-blasting (for bitvectors) or direct encoding (for booleans).

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use crate::ast::{Command, Sort, Term};
use crate::bitvector::{BitBlaster, BitVec};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::sat::{Lit, SatResult, SatSolver};

/// A typed value in the solver
#[derive(Debug, Clone)]
enum Value {
    Bool(Lit),
    BitVector(BitVec),
}

/// Stack frame for push/pop
struct Frame {
    var_snapshot: Vec<(String, Option<Value>)>,
    defined_snapshot: Vec<(String, Option<(Vec<(String, Sort)>, Term)>)>,
}

pub struct SmtSolver {
    sat: SatSolver,
    variables: HashMap<String, Value>,
    var_sorts: HashMap<String, Sort>,
    defined_funs: HashMap<String, (Vec<(String, Sort)>, Term)>,
    stack: Vec<Frame>,
    logic: Option<String>,
    produce_models: bool,
}

impl SmtSolver {
    pub fn new() -> Self {
        SmtSolver {
            sat: SatSolver::new(),
            variables: HashMap::new(),
            var_sorts: HashMap::new(),
            defined_funs: HashMap::new(),
            stack: Vec::new(),
            logic: None,
            produce_models: false,
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

                    // Try to parse when we have balanced parens
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

    fn execute_command(&mut self, cmd: Command) -> Result<Option<String>, String> {
        match cmd {
            Command::SetLogic(logic) => {
                match logic.as_str() {
                    "QF_BV" | "QF_UF" | "QF_UFBV" | "QF_LIA" | "ALL" | "HORN" => {}
                    other => {
                        // Accept but warn about unsupported logics
                        if !other.contains("BV") && other != "QF_UF" && other != "ALL" {
                            // Still accept it
                        }
                    }
                }
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
                self.defined_funs.insert(name, (params, body));
                Ok(None)
            }
            Command::Assert(term) => {
                let lit = self.encode_bool_term(&term)?;
                self.sat.add_clause(vec![lit]);
                Ok(None)
            }
            Command::CheckSat => {
                let result = self.sat.solve();
                Ok(Some(match result {
                    SatResult::Sat => "sat".to_string(),
                    SatResult::Unsat => "unsat".to_string(),
                    SatResult::Unknown => "unknown".to_string(),
                }))
            }
            Command::GetModel => {
                let mut model = String::from("(\n");
                let mut sorted_vars: Vec<_> = self.var_sorts.iter().collect();
                sorted_vars.sort_by_key(|(name, _)| name.clone());
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
                                    None => "true", // default
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
                                Some(v) => {
                                    self.variables.insert(name, v);
                                }
                                None => {
                                    self.variables.remove(&name);
                                }
                            }
                        }
                        for (name, old_def) in frame.defined_snapshot.into_iter().rev() {
                            match old_def {
                                Some(d) => {
                                    self.defined_funs.insert(name, d);
                                }
                                None => {
                                    self.defined_funs.remove(&name);
                                }
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
                self.variables.clear();
                self.var_sorts.clear();
                self.stack.clear();
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
                // Check if it's a defined function with no args
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
                // Tseitin: r <=> (l1 AND l2 AND ...)
                let r = self.sat.new_var() as Lit;
                // r => li: for each li, (-r OR li)
                for &l in &lits {
                    self.sat.add_clause(vec![-r, l]);
                }
                // l1 AND l2 AND ... => r
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
                // r => (l1 OR l2 OR ...): (-r OR l1 OR l2 OR ...)
                let mut clause = vec![-r];
                clause.extend_from_slice(&lits);
                self.sat.add_clause(clause);
                // li => r: for each li, (-li OR r)
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
                // r <=> (!a OR b)
                // r => (!a OR b): (-r OR -a OR b)
                self.sat.add_clause(vec![-r, -la, lb]);
                // (!a OR b) => r: (a OR r) AND (-b OR r)
                self.sat.add_clause(vec![la, r]);
                self.sat.add_clause(vec![-lb, r]);
                Ok(r)
            }
            Term::Ite(cond, then_t, else_t) => {
                let cond_sort = self.infer_sort(cond);
                let then_sort = self.infer_sort(then_t);

                if then_sort == Some(Sort::Bool) || cond_sort == Some(Sort::Bool) {
                    // Check if then/else are booleans
                    if let (Ok(lt), Ok(le)) = (
                        self.encode_bool_term(then_t),
                        self.encode_bool_term(else_t),
                    ) {
                        let lc = self.encode_bool_term(cond)?;
                        let r = self.sat.new_var() as Lit;
                        // cond => (r <=> then)
                        self.sat.add_clause(vec![-lc, -r, lt]);
                        self.sat.add_clause(vec![-lc, r, -lt]);
                        // !cond => (r <=> else)
                        self.sat.add_clause(vec![lc, -r, le]);
                        self.sat.add_clause(vec![lc, r, -le]);
                        return Ok(r);
                    }
                }

                Err("ite with bitvector result used in boolean context".into())
            }
            Term::Eq(a, b) => {
                // Could be Bool = Bool or BV = BV
                let sort_a = self.infer_sort(a);
                let sort_b = self.infer_sort(b);
                match (&sort_a, &sort_b) {
                    (Some(Sort::Bool), _) | (_, Some(Sort::Bool)) => {
                        let la = self.encode_bool_term(a)?;
                        let lb = self.encode_bool_term(b)?;
                        // r <=> (a XNOR b)
                        let r = self.sat.new_var() as Lit;
                        self.sat.add_clause(vec![-r, -la, lb]);
                        self.sat.add_clause(vec![-r, la, -lb]);
                        self.sat.add_clause(vec![r, -la, -lb]);
                        self.sat.add_clause(vec![r, la, lb]);
                        Ok(r)
                    }
                    _ => {
                        // Try bitvector
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
                // Save old bindings
                let mut saved = Vec::new();
                for (name, val_term) in bindings {
                    let old = self.variables.get(name).cloned();
                    saved.push((name.clone(), old));

                    // Determine sort of the binding
                    let sort = self.infer_sort(val_term);
                    match sort {
                        Some(Sort::Bool) | None => {
                            // Try bool first
                            match self.encode_bool_term(val_term) {
                                Ok(lit) => {
                                    self.variables
                                        .insert(name.clone(), Value::Bool(lit));
                                    self.var_sorts
                                        .insert(name.clone(), Sort::Bool);
                                }
                                Err(_) => {
                                    // Try BV
                                    let bv = self.encode_bv_term(val_term)?;
                                    let w = bv.width();
                                    self.variables
                                        .insert(name.clone(), Value::BitVector(bv));
                                    self.var_sorts
                                        .insert(name.clone(), Sort::BitVec(w));
                                }
                            }
                        }
                        Some(Sort::BitVec(_)) => {
                            let bv = self.encode_bv_term(val_term)?;
                            let w = bv.width();
                            self.variables
                                .insert(name.clone(), Value::BitVector(bv));
                            self.var_sorts
                                .insert(name.clone(), Sort::BitVec(w));
                        }
                    }
                }

                let result = self.encode_bool_term(body);

                // Restore bindings
                for (name, old) in saved.into_iter().rev() {
                    match old {
                        Some(v) => {
                            self.variables.insert(name, v);
                        }
                        None => {
                            self.variables.remove(&name);
                        }
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
                    // cond => (r <=> then[i])
                    self.sat.add_clause(vec![-cond_lit, -r, then_bv.bits[i]]);
                    self.sat.add_clause(vec![-cond_lit, r, -then_bv.bits[i]]);
                    // !cond => (r <=> else[i])
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
            Term::Variable(name) => self.var_sorts.get(name).cloned(),
            Term::Not(_) | Term::And(_) | Term::Or(_) | Term::Xor(_, _)
            | Term::Implies(_, _) => Some(Sort::Bool),
            Term::Eq(_, _) | Term::Distinct(_, _) => Some(Sort::Bool),
            Term::BvUlt(_, _) | Term::BvUle(_, _) | Term::BvUgt(_, _) | Term::BvUge(_, _)
            | Term::BvSlt(_, _) | Term::BvSle(_, _) | Term::BvSgt(_, _) | Term::BvSge(_, _) => {
                Some(Sort::Bool)
            }
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
                None => Err(format!("unknown variable: {}", name)),
            },
            _ => Err("get-value only supports variables".into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(input: &str) -> Vec<String> {
        let mut solver = SmtSolver::new();
        solver.process_input(input).unwrap()
    }

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
        assert!(result[1].contains("bv66 8")); // 0x42 = 66
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
        assert_eq!(result, vec!["sat"]); // 3 * 7 = 21 = 0x15
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
}

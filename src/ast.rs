use std::fmt;

/// SMT-LIB sorts
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    BitVec(u32),
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::BitVec(w) => write!(f, "(_ BitVec {})", w),
        }
    }
}

/// Terms in the SMT-LIB language
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    // Constants
    True,
    False,
    BitVecLiteral { value: u64, width: u32 },

    // Variables
    Variable(String),

    // Boolean operations
    Not(Box<Term>),
    And(Vec<Term>),
    Or(Vec<Term>),
    Xor(Box<Term>, Box<Term>),
    Implies(Box<Term>, Box<Term>),
    Ite(Box<Term>, Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Distinct(Box<Term>, Box<Term>),

    // Bitvector arithmetic
    BvNot(Box<Term>),
    BvAnd(Box<Term>, Box<Term>),
    BvOr(Box<Term>, Box<Term>),
    BvXor(Box<Term>, Box<Term>),
    BvNeg(Box<Term>),
    BvAdd(Box<Term>, Box<Term>),
    BvSub(Box<Term>, Box<Term>),
    BvMul(Box<Term>, Box<Term>),
    BvUdiv(Box<Term>, Box<Term>),
    BvUrem(Box<Term>, Box<Term>),
    BvSdiv(Box<Term>, Box<Term>),
    BvSrem(Box<Term>, Box<Term>),
    BvShl(Box<Term>, Box<Term>),
    BvLshr(Box<Term>, Box<Term>),
    BvAshr(Box<Term>, Box<Term>),

    // Bitvector comparisons
    BvUlt(Box<Term>, Box<Term>),
    BvUle(Box<Term>, Box<Term>),
    BvUgt(Box<Term>, Box<Term>),
    BvUge(Box<Term>, Box<Term>),
    BvSlt(Box<Term>, Box<Term>),
    BvSle(Box<Term>, Box<Term>),
    BvSgt(Box<Term>, Box<Term>),
    BvSge(Box<Term>, Box<Term>),

    // Bitvector operations
    Concat(Box<Term>, Box<Term>),
    Extract { high: u32, low: u32, term: Box<Term> },
    ZeroExtend(u32, Box<Term>),
    SignExtend(u32, Box<Term>),

    // Let binding
    Let { bindings: Vec<(String, Term)>, body: Box<Term> },
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::True => write!(f, "true"),
            Term::False => write!(f, "false"),
            Term::BitVecLiteral { value, width } => {
                write!(f, "(_ bv{} {})", value, width)
            }
            Term::Variable(name) => write!(f, "{}", name),
            Term::Not(t) => write!(f, "(not {})", t),
            Term::And(ts) => {
                write!(f, "(and")?;
                for t in ts {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Term::Or(ts) => {
                write!(f, "(or")?;
                for t in ts {
                    write!(f, " {}", t)?;
                }
                write!(f, ")")
            }
            Term::Xor(a, b) => write!(f, "(xor {} {})", a, b),
            Term::Implies(a, b) => write!(f, "(=> {} {})", a, b),
            Term::Ite(c, t, e) => write!(f, "(ite {} {} {})", c, t, e),
            Term::Eq(a, b) => write!(f, "(= {} {})", a, b),
            Term::Distinct(a, b) => write!(f, "(distinct {} {})", a, b),
            Term::BvAdd(a, b) => write!(f, "(bvadd {} {})", a, b),
            Term::BvSub(a, b) => write!(f, "(bvsub {} {})", a, b),
            Term::BvMul(a, b) => write!(f, "(bvmul {} {})", a, b),
            Term::BvAnd(a, b) => write!(f, "(bvand {} {})", a, b),
            Term::BvOr(a, b) => write!(f, "(bvor {} {})", a, b),
            Term::BvXor(a, b) => write!(f, "(bvxor {} {})", a, b),
            Term::BvNot(t) => write!(f, "(bvnot {})", t),
            Term::BvNeg(t) => write!(f, "(bvneg {})", t),
            Term::BvUdiv(a, b) => write!(f, "(bvudiv {} {})", a, b),
            Term::BvUrem(a, b) => write!(f, "(bvurem {} {})", a, b),
            Term::BvSdiv(a, b) => write!(f, "(bvsdiv {} {})", a, b),
            Term::BvSrem(a, b) => write!(f, "(bvsrem {} {})", a, b),
            Term::BvShl(a, b) => write!(f, "(bvshl {} {})", a, b),
            Term::BvLshr(a, b) => write!(f, "(bvlshr {} {})", a, b),
            Term::BvAshr(a, b) => write!(f, "(bvashr {} {})", a, b),
            Term::BvUlt(a, b) => write!(f, "(bvult {} {})", a, b),
            Term::BvUle(a, b) => write!(f, "(bvule {} {})", a, b),
            Term::BvUgt(a, b) => write!(f, "(bvugt {} {})", a, b),
            Term::BvUge(a, b) => write!(f, "(bvuge {} {})", a, b),
            Term::BvSlt(a, b) => write!(f, "(bvslt {} {})", a, b),
            Term::BvSle(a, b) => write!(f, "(bvsle {} {})", a, b),
            Term::BvSgt(a, b) => write!(f, "(bvsgt {} {})", a, b),
            Term::BvSge(a, b) => write!(f, "(bvsge {} {})", a, b),
            Term::Concat(a, b) => write!(f, "(concat {} {})", a, b),
            Term::Extract { high, low, term } => {
                write!(f, "((_ extract {} {}) {})", high, low, term)
            }
            Term::ZeroExtend(n, t) => write!(f, "((_ zero_extend {}) {})", n, t),
            Term::SignExtend(n, t) => write!(f, "((_ sign_extend {}) {})", n, t),
            Term::Let { bindings, body } => {
                write!(f, "(let (")?;
                for (name, val) in bindings {
                    write!(f, "({} {})", name, val)?;
                }
                write!(f, ") {})", body)
            }
        }
    }
}

/// SMT-LIB commands
#[derive(Debug, Clone)]
pub enum Command {
    SetLogic(String),
    SetOption(String, String),
    SetInfo(String, String),
    DeclareConst(String, Sort),
    DeclareFun(String, Vec<Sort>, Sort),
    DefineFun(String, Vec<(String, Sort)>, Sort, Term),
    Assert(Term),
    CheckSat,
    GetModel,
    GetValue(Vec<Term>),
    Push(u32),
    Pop(u32),
    Reset,
    ResetAssertions,
    Exit,
    Echo(String),
}

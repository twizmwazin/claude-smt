use std::fmt;

/// SMT-LIB sorts
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    BitVec(u32),
    Int,
    Real,
    String,
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::BitVec(w) => write!(f, "(_ BitVec {})", w),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::String => write!(f, "String"),
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
    IntLiteral(i64),
    RealLiteral(i64, i64), // numerator, denominator (exact rational)
    StringLiteral(String),

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

    // Int/Real arithmetic (shared operators per SMT-LIB)
    Neg(Box<Term>),
    Add(Vec<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Vec<Term>),
    Div(Box<Term>, Box<Term>),
    Mod(Box<Term>, Box<Term>),
    Abs(Box<Term>),

    // Int/Real comparisons
    Lt(Box<Term>, Box<Term>),
    Le(Box<Term>, Box<Term>),
    Gt(Box<Term>, Box<Term>),
    Ge(Box<Term>, Box<Term>),

    // Int-specific
    ToReal(Box<Term>),
    ToInt(Box<Term>),
    IsInt(Box<Term>),
    Divisible(u64, Box<Term>),

    // String operations
    StrLen(Box<Term>),
    StrConcat(Vec<Term>),
    StrAt(Box<Term>, Box<Term>),
    StrSubstr(Box<Term>, Box<Term>, Box<Term>),
    StrContains(Box<Term>, Box<Term>),
    StrIndexOf(Box<Term>, Box<Term>, Box<Term>),
    StrReplace(Box<Term>, Box<Term>, Box<Term>),
    StrPrefixOf(Box<Term>, Box<Term>),
    StrSuffixOf(Box<Term>, Box<Term>),
    StrToInt(Box<Term>),
    IntToStr(Box<Term>),
    StrLt(Box<Term>, Box<Term>),
    StrLe(Box<Term>, Box<Term>),

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
            Term::IntLiteral(n) => {
                if *n < 0 {
                    write!(f, "(- {})", -n)
                } else {
                    write!(f, "{}", n)
                }
            }
            Term::RealLiteral(num, den) => {
                if *den == 1 {
                    if *num < 0 {
                        write!(f, "(- {}.0)", -num)
                    } else {
                        write!(f, "{}.0", num)
                    }
                } else {
                    write!(f, "(/ {} {})", num, den)
                }
            }
            Term::StringLiteral(s) => write!(f, "\"{}\"", s),
            Term::Variable(name) => write!(f, "{}", name),
            Term::Not(t) => write!(f, "(not {})", t),
            Term::And(ts) => {
                write!(f, "(and")?;
                for t in ts { write!(f, " {}", t)?; }
                write!(f, ")")
            }
            Term::Or(ts) => {
                write!(f, "(or")?;
                for t in ts { write!(f, " {}", t)?; }
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
            Term::Neg(t) => write!(f, "(- {})", t),
            Term::Add(ts) => {
                write!(f, "(+")?;
                for t in ts { write!(f, " {}", t)?; }
                write!(f, ")")
            }
            Term::Sub(a, b) => write!(f, "(- {} {})", a, b),
            Term::Mul(ts) => {
                write!(f, "(*")?;
                for t in ts { write!(f, " {}", t)?; }
                write!(f, ")")
            }
            Term::Div(a, b) => write!(f, "(div {} {})", a, b),
            Term::Mod(a, b) => write!(f, "(mod {} {})", a, b),
            Term::Abs(t) => write!(f, "(abs {})", t),
            Term::Lt(a, b) => write!(f, "(< {} {})", a, b),
            Term::Le(a, b) => write!(f, "(<= {} {})", a, b),
            Term::Gt(a, b) => write!(f, "(> {} {})", a, b),
            Term::Ge(a, b) => write!(f, "(>= {} {})", a, b),
            Term::ToReal(t) => write!(f, "(to_real {})", t),
            Term::ToInt(t) => write!(f, "(to_int {})", t),
            Term::IsInt(t) => write!(f, "(is_int {})", t),
            Term::Divisible(n, t) => write!(f, "((_ divisible {}) {})", n, t),
            Term::StrLen(t) => write!(f, "(str.len {})", t),
            Term::StrConcat(ts) => {
                write!(f, "(str.++")?;
                for t in ts { write!(f, " {}", t)?; }
                write!(f, ")")
            }
            Term::StrAt(s, i) => write!(f, "(str.at {} {})", s, i),
            Term::StrSubstr(s, i, l) => write!(f, "(str.substr {} {} {})", s, i, l),
            Term::StrContains(a, b) => write!(f, "(str.contains {} {})", a, b),
            Term::StrIndexOf(s, t, i) => write!(f, "(str.indexof {} {} {})", s, t, i),
            Term::StrReplace(s, a, b) => write!(f, "(str.replace {} {} {})", s, a, b),
            Term::StrPrefixOf(a, b) => write!(f, "(str.prefixof {} {})", a, b),
            Term::StrSuffixOf(a, b) => write!(f, "(str.suffixof {} {})", a, b),
            Term::StrToInt(t) => write!(f, "(str.to_int {})", t),
            Term::IntToStr(t) => write!(f, "(int.to.str {})", t),
            Term::StrLt(a, b) => write!(f, "(str.< {} {})", a, b),
            Term::StrLe(a, b) => write!(f, "(str.<= {} {})", a, b),
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

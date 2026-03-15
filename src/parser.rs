use crate::ast::{Command, Sort, Term};
use crate::lexer::Token;
use std::fmt;

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Parse error: {}", self.message)
    }
}

impl ParseError {
    fn new(msg: impl Into<String>) -> Self {
        ParseError { message: msg.into() }
    }
}

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn advance(&mut self) -> Result<&Token, ParseError> {
        if self.pos < self.tokens.len() {
            let tok = &self.tokens[self.pos];
            self.pos += 1;
            Ok(tok)
        } else {
            Err(ParseError::new("unexpected end of input"))
        }
    }

    fn expect_lparen(&mut self) -> Result<(), ParseError> {
        match self.advance()? {
            Token::LParen => Ok(()),
            tok => Err(ParseError::new(format!("expected '(', got '{}'", tok))),
        }
    }

    fn expect_rparen(&mut self) -> Result<(), ParseError> {
        match self.advance()? {
            Token::RParen => Ok(()),
            tok => Err(ParseError::new(format!("expected ')', got '{}'", tok))),
        }
    }

    fn expect_symbol(&mut self) -> Result<String, ParseError> {
        match self.advance()?.clone() {
            Token::Symbol(s) => Ok(s),
            tok => Err(ParseError::new(format!("expected symbol, got '{}'", tok))),
        }
    }

    fn expect_numeral(&mut self) -> Result<u64, ParseError> {
        match self.advance()?.clone() {
            Token::Numeral(n) => n
                .parse::<u64>()
                .map_err(|_| ParseError::new(format!("invalid numeral: {}", n))),
            tok => Err(ParseError::new(format!("expected numeral, got '{}'", tok))),
        }
    }

    pub fn parse_commands(&mut self) -> Result<Vec<Command>, ParseError> {
        let mut commands = Vec::new();
        while self.pos < self.tokens.len() {
            commands.push(self.parse_command()?);
        }
        Ok(commands)
    }

    fn parse_command(&mut self) -> Result<Command, ParseError> {
        self.expect_lparen()?;
        let cmd_name = self.expect_symbol()?;

        let cmd = match cmd_name.as_str() {
            "set-logic" => {
                let logic = self.expect_symbol()?;
                Command::SetLogic(logic)
            }
            "set-option" => {
                let key = match self.advance()?.clone() {
                    Token::Keyword(k) => k,
                    tok => return Err(ParseError::new(format!("expected keyword, got '{}'", tok))),
                };
                let val = match self.advance()?.clone() {
                    Token::Symbol(s) => s,
                    Token::Numeral(n) => n,
                    Token::StringLiteral(s) => s,
                    tok => return Err(ParseError::new(format!("expected value, got '{}'", tok))),
                };
                Command::SetOption(key, val)
            }
            "set-info" => {
                let key = match self.advance()?.clone() {
                    Token::Keyword(k) => k,
                    tok => return Err(ParseError::new(format!("expected keyword, got '{}'", tok))),
                };
                let val = match self.advance()?.clone() {
                    Token::Symbol(s) => s,
                    Token::Numeral(n) => n,
                    Token::StringLiteral(s) => s,
                    tok => return Err(ParseError::new(format!("expected value, got '{}'", tok))),
                };
                Command::SetInfo(key, val)
            }
            "declare-const" => {
                let name = self.expect_symbol()?;
                let sort = self.parse_sort()?;
                Command::DeclareConst(name, sort)
            }
            "declare-fun" => {
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut arg_sorts = Vec::new();
                while self.peek() != Some(&Token::RParen) {
                    arg_sorts.push(self.parse_sort()?);
                }
                self.expect_rparen()?;
                let ret_sort = self.parse_sort()?;
                Command::DeclareFun(name, arg_sorts, ret_sort)
            }
            "define-fun" => {
                let name = self.expect_symbol()?;
                self.expect_lparen()?;
                let mut params = Vec::new();
                while self.peek() != Some(&Token::RParen) {
                    self.expect_lparen()?;
                    let pname = self.expect_symbol()?;
                    let psort = self.parse_sort()?;
                    self.expect_rparen()?;
                    params.push((pname, psort));
                }
                self.expect_rparen()?;
                let ret_sort = self.parse_sort()?;
                let body = self.parse_term()?;
                Command::DefineFun(name, params, ret_sort, body)
            }
            "assert" => {
                let term = self.parse_term()?;
                Command::Assert(term)
            }
            "check-sat" => Command::CheckSat,
            "get-model" => Command::GetModel,
            "get-value" => {
                self.expect_lparen()?;
                let mut terms = Vec::new();
                while self.peek() != Some(&Token::RParen) {
                    terms.push(self.parse_term()?);
                }
                self.expect_rparen()?;
                Command::GetValue(terms)
            }
            "push" => {
                let n = if self.peek() == Some(&Token::RParen) {
                    1
                } else {
                    self.expect_numeral()? as u32
                };
                Command::Push(n)
            }
            "pop" => {
                let n = if self.peek() == Some(&Token::RParen) {
                    1
                } else {
                    self.expect_numeral()? as u32
                };
                Command::Pop(n)
            }
            "reset" => Command::Reset,
            "reset-assertions" => Command::ResetAssertions,
            "exit" => Command::Exit,
            "echo" => {
                let msg = match self.advance()?.clone() {
                    Token::StringLiteral(s) => s,
                    tok => return Err(ParseError::new(format!("expected string, got '{}'", tok))),
                };
                Command::Echo(msg)
            }
            other => {
                return Err(ParseError::new(format!("unknown command: {}", other)));
            }
        };

        self.expect_rparen()?;
        Ok(cmd)
    }

    fn parse_sort(&mut self) -> Result<Sort, ParseError> {
        match self.peek().cloned() {
            Some(Token::Symbol(ref s)) if s == "Bool" => {
                self.advance()?;
                Ok(Sort::Bool)
            }
            Some(Token::LParen) => {
                self.advance()?; // (
                let underscore = self.expect_symbol()?;
                if underscore != "_" {
                    return Err(ParseError::new(format!(
                        "expected '_' in indexed sort, got '{}'",
                        underscore
                    )));
                }
                let name = self.expect_symbol()?;
                match name.as_str() {
                    "BitVec" => {
                        let width = self.expect_numeral()? as u32;
                        self.expect_rparen()?;
                        Ok(Sort::BitVec(width))
                    }
                    other => Err(ParseError::new(format!("unknown indexed sort: {}", other))),
                }
            }
            Some(tok) => Err(ParseError::new(format!("expected sort, got '{}'", tok))),
            None => Err(ParseError::new("expected sort, got end of input")),
        }
    }

    fn parse_term(&mut self) -> Result<Term, ParseError> {
        match self.peek().cloned() {
            Some(Token::Symbol(ref s)) => {
                let s = s.clone();
                self.advance()?;
                match s.as_str() {
                    "true" => Ok(Term::True),
                    "false" => Ok(Term::False),
                    _ => Ok(Term::Variable(s)),
                }
            }
            Some(Token::Numeral(ref n)) => {
                let n = n.clone();
                self.advance()?;
                // Bare numerals in Bool context are not standard, but we keep them
                // They'll be resolved during type checking
                Ok(Term::BitVecLiteral {
                    value: n.parse::<u64>().map_err(|_| ParseError::new("invalid numeral"))?,
                    width: 0, // width unknown, to be resolved
                })
            }
            Some(Token::HexLiteral(ref h)) => {
                let h = h.clone();
                self.advance()?;
                let value = u64::from_str_radix(&h, 16)
                    .map_err(|_| ParseError::new(format!("invalid hex literal: {}", h)))?;
                let width = (h.len() * 4) as u32;
                Ok(Term::BitVecLiteral { value, width })
            }
            Some(Token::BinLiteral(ref b)) => {
                let b = b.clone();
                self.advance()?;
                let value = u64::from_str_radix(&b, 2)
                    .map_err(|_| ParseError::new(format!("invalid binary literal: {}", b)))?;
                let width = b.len() as u32;
                Ok(Term::BitVecLiteral { value, width })
            }
            Some(Token::LParen) => self.parse_compound_term(),
            Some(tok) => Err(ParseError::new(format!("expected term, got '{}'", tok))),
            None => Err(ParseError::new("expected term, got end of input")),
        }
    }

    fn parse_compound_term(&mut self) -> Result<Term, ParseError> {
        self.expect_lparen()?;

        // Check for indexed operator (_ op indices...)
        if self.peek() == Some(&Token::LParen) {
            // Could be ((_ extract hi lo) term) or ((_ zero_extend n) term) etc.
            let saved_pos = self.pos;
            self.advance()?; // skip (
            if self.peek() == Some(&Token::Symbol("_".to_string())) {
                self.advance()?; // skip _
                let op = self.expect_symbol()?;
                return self.parse_indexed_op(&op);
            } else {
                // Not an indexed op, restore position
                self.pos = saved_pos;
            }
        }

        let head = match self.peek().cloned() {
            Some(Token::Symbol(s)) => {
                self.advance()?;
                s
            }
            Some(Token::LParen) => {
                // This shouldn't happen for well-formed SMT-LIB
                return Err(ParseError::new("unexpected '(' in operator position"));
            }
            Some(tok) => return Err(ParseError::new(format!("expected operator, got '{}'", tok))),
            None => return Err(ParseError::new("expected operator")),
        };

        match head.as_str() {
            // Special form: (_ bvN W) - bitvector literal
            "_" => {
                let bv_sym = self.expect_symbol()?;
                if let Some(stripped) = bv_sym.strip_prefix("bv") {
                    let value: u64 = stripped
                        .parse()
                        .map_err(|_| ParseError::new("invalid bv literal value"))?;
                    let width = self.expect_numeral()? as u32;
                    self.expect_rparen()?;
                    Ok(Term::BitVecLiteral { value, width })
                } else {
                    Err(ParseError::new(format!("unknown indexed identifier: {}", bv_sym)))
                }
            }

            "let" => {
                self.expect_lparen()?;
                let mut bindings = Vec::new();
                while self.peek() != Some(&Token::RParen) {
                    self.expect_lparen()?;
                    let name = self.expect_symbol()?;
                    let val = self.parse_term()?;
                    self.expect_rparen()?;
                    bindings.push((name, val));
                }
                self.expect_rparen()?;
                let body = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Let {
                    bindings,
                    body: Box::new(body),
                })
            }

            // Boolean ops
            "not" => {
                let t = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Not(Box::new(t)))
            }
            "and" => {
                let args = self.parse_term_list()?;
                Ok(Term::And(args))
            }
            "or" => {
                let args = self.parse_term_list()?;
                Ok(Term::Or(args))
            }
            "xor" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Xor(Box::new(a), Box::new(b)))
            }
            "=>" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Implies(Box::new(a), Box::new(b)))
            }
            "ite" => {
                let c = self.parse_term()?;
                let t = self.parse_term()?;
                let e = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Ite(Box::new(c), Box::new(t), Box::new(e)))
            }
            "=" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Eq(Box::new(a), Box::new(b)))
            }
            "distinct" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Distinct(Box::new(a), Box::new(b)))
            }

            // Bitvector ops
            "bvnot" => {
                let t = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvNot(Box::new(t)))
            }
            "bvand" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvAnd(Box::new(a), Box::new(b)))
            }
            "bvor" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvOr(Box::new(a), Box::new(b)))
            }
            "bvxor" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvXor(Box::new(a), Box::new(b)))
            }
            "bvneg" => {
                let t = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvNeg(Box::new(t)))
            }
            "bvadd" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvAdd(Box::new(a), Box::new(b)))
            }
            "bvsub" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvSub(Box::new(a), Box::new(b)))
            }
            "bvmul" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvMul(Box::new(a), Box::new(b)))
            }
            "bvudiv" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvUdiv(Box::new(a), Box::new(b)))
            }
            "bvurem" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvUrem(Box::new(a), Box::new(b)))
            }
            "bvsdiv" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvSdiv(Box::new(a), Box::new(b)))
            }
            "bvsrem" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvSrem(Box::new(a), Box::new(b)))
            }
            "bvshl" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvShl(Box::new(a), Box::new(b)))
            }
            "bvlshr" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvLshr(Box::new(a), Box::new(b)))
            }
            "bvashr" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvAshr(Box::new(a), Box::new(b)))
            }
            "bvult" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvUlt(Box::new(a), Box::new(b)))
            }
            "bvule" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvUle(Box::new(a), Box::new(b)))
            }
            "bvugt" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvUgt(Box::new(a), Box::new(b)))
            }
            "bvuge" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvUge(Box::new(a), Box::new(b)))
            }
            "bvslt" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvSlt(Box::new(a), Box::new(b)))
            }
            "bvsle" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvSle(Box::new(a), Box::new(b)))
            }
            "bvsgt" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvSgt(Box::new(a), Box::new(b)))
            }
            "bvsge" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::BvSge(Box::new(a), Box::new(b)))
            }
            "concat" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::Concat(Box::new(a), Box::new(b)))
            }

            other => Err(ParseError::new(format!("unknown function: {}", other))),
        }
    }

    fn parse_indexed_op(&mut self, op: &str) -> Result<Term, ParseError> {
        match op {
            "extract" => {
                let high = self.expect_numeral()? as u32;
                let low = self.expect_numeral()? as u32;
                self.expect_rparen()?; // close (_ extract h l)
                let term = self.parse_term()?;
                self.expect_rparen()?; // close outer
                Ok(Term::Extract {
                    high,
                    low,
                    term: Box::new(term),
                })
            }
            "zero_extend" => {
                let n = self.expect_numeral()? as u32;
                self.expect_rparen()?;
                let term = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::ZeroExtend(n, Box::new(term)))
            }
            "sign_extend" => {
                let n = self.expect_numeral()? as u32;
                self.expect_rparen()?;
                let term = self.parse_term()?;
                self.expect_rparen()?;
                Ok(Term::SignExtend(n, Box::new(term)))
            }
            other => Err(ParseError::new(format!("unknown indexed operator: {}", other))),
        }
    }

    fn parse_term_list(&mut self) -> Result<Vec<Term>, ParseError> {
        let mut terms = Vec::new();
        while self.peek() != Some(&Token::RParen) {
            terms.push(self.parse_term()?);
        }
        self.expect_rparen()?;
        Ok(terms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;

    fn parse(input: &str) -> Vec<Command> {
        let mut lexer = Lexer::new(input);
        let tokens = lexer.tokenize().unwrap();
        let mut parser = Parser::new(tokens);
        parser.parse_commands().unwrap()
    }

    #[test]
    fn test_declare_const() {
        let cmds = parse("(declare-const x Bool)");
        assert_eq!(cmds.len(), 1);
        match &cmds[0] {
            Command::DeclareConst(name, sort) => {
                assert_eq!(name, "x");
                assert_eq!(*sort, Sort::Bool);
            }
            _ => panic!("expected DeclareConst"),
        }
    }

    #[test]
    fn test_declare_bv() {
        let cmds = parse("(declare-const x (_ BitVec 32))");
        assert_eq!(cmds.len(), 1);
        match &cmds[0] {
            Command::DeclareConst(name, sort) => {
                assert_eq!(name, "x");
                assert_eq!(*sort, Sort::BitVec(32));
            }
            _ => panic!("expected DeclareConst"),
        }
    }

    #[test]
    fn test_assert_bool() {
        let cmds = parse("(assert (and x (not y)))");
        assert_eq!(cmds.len(), 1);
        match &cmds[0] {
            Command::Assert(Term::And(args)) => {
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Assert with And"),
        }
    }

    #[test]
    fn test_bv_operations() {
        let cmds = parse("(assert (= (bvadd x y) #xFF))");
        assert_eq!(cmds.len(), 1);
    }

    #[test]
    fn test_extract() {
        let cmds = parse("(assert (= ((_ extract 7 0) x) #xFF))");
        assert_eq!(cmds.len(), 1);
    }

    #[test]
    fn test_let_binding() {
        let cmds = parse("(assert (let ((a true)) a))");
        assert_eq!(cmds.len(), 1);
        match &cmds[0] {
            Command::Assert(Term::Let { bindings, body: _ }) => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "a");
            }
            _ => panic!("expected Assert with Let"),
        }
    }

    #[test]
    fn test_full_program() {
        let input = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvadd x y) #xFF))
            (check-sat)
            (exit)
        "#;
        let cmds = parse(input);
        assert_eq!(cmds.len(), 6);
    }
}

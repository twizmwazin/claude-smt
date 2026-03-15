use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Symbol(String),
    Keyword(String),
    Numeral(String),
    HexLiteral(String),   // #xABCD
    BinLiteral(String),   // #b0101
    StringLiteral(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::Symbol(s) => write!(f, "{}", s),
            Token::Keyword(k) => write!(f, ":{}", k),
            Token::Numeral(n) => write!(f, "{}", n),
            Token::HexLiteral(h) => write!(f, "#x{}", h),
            Token::BinLiteral(b) => write!(f, "#b{}", b),
            Token::StringLiteral(s) => write!(f, "\"{}\"", s),
        }
    }
}

#[derive(Debug)]
pub struct LexError {
    pub message: String,
    pub position: usize,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Lexer error at position {}: {}", self.position, self.message)
    }
}

pub struct Lexer<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            input: input.as_bytes(),
            pos: 0,
        }
    }

    pub fn tokenize(&mut self) -> Result<Vec<Token>, LexError> {
        let mut tokens = Vec::new();
        while let Some(tok) = self.next_token()? {
            tokens.push(tok);
        }
        Ok(tokens)
    }

    fn peek(&self) -> Option<u8> {
        if self.pos < self.input.len() {
            Some(self.input[self.pos])
        } else {
            None
        }
    }

    fn advance(&mut self) -> Option<u8> {
        if self.pos < self.input.len() {
            let ch = self.input[self.pos];
            self.pos += 1;
            Some(ch)
        } else {
            None
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while self.pos < self.input.len() && self.input[self.pos].is_ascii_whitespace() {
                self.pos += 1;
            }
            // Skip line comments
            if self.pos < self.input.len() && self.input[self.pos] == b';' {
                while self.pos < self.input.len() && self.input[self.pos] != b'\n' {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    fn is_symbol_char(ch: u8) -> bool {
        ch.is_ascii_alphanumeric()
            || matches!(
                ch,
                b'+' | b'-' | b'/' | b'*' | b'=' | b'%' | b'?' | b'!' | b'.'
                | b'$' | b'_' | b'~' | b'&' | b'^' | b'<' | b'>' | b'@'
            )
    }

    fn next_token(&mut self) -> Result<Option<Token>, LexError> {
        self.skip_whitespace_and_comments();

        match self.peek() {
            None => Ok(None),
            Some(b'(') => {
                self.advance();
                Ok(Some(Token::LParen))
            }
            Some(b')') => {
                self.advance();
                Ok(Some(Token::RParen))
            }
            Some(b'"') => self.read_string(),
            Some(b'#') => self.read_hash_literal(),
            Some(b':') => self.read_keyword(),
            Some(b'|') => self.read_quoted_symbol(),
            Some(ch) if ch.is_ascii_digit() => self.read_numeral(),
            Some(ch) if Self::is_symbol_char(ch) => self.read_symbol(),
            Some(ch) => Err(LexError {
                message: format!("unexpected character: '{}'", ch as char),
                position: self.pos,
            }),
        }
    }

    fn read_string(&mut self) -> Result<Option<Token>, LexError> {
        self.advance(); // skip opening quote
        let mut s = String::new();
        loop {
            match self.advance() {
                None => {
                    return Err(LexError {
                        message: "unterminated string literal".into(),
                        position: self.pos,
                    })
                }
                Some(b'"') => {
                    // Check for escaped quote ""
                    if self.peek() == Some(b'"') {
                        self.advance();
                        s.push('"');
                    } else {
                        return Ok(Some(Token::StringLiteral(s)));
                    }
                }
                Some(ch) => s.push(ch as char),
            }
        }
    }

    fn read_hash_literal(&mut self) -> Result<Option<Token>, LexError> {
        let start = self.pos;
        self.advance(); // skip #
        match self.peek() {
            Some(b'x') | Some(b'X') => {
                self.advance();
                let mut hex = String::new();
                while let Some(ch) = self.peek() {
                    if ch.is_ascii_hexdigit() {
                        hex.push(ch as char);
                        self.advance();
                    } else {
                        break;
                    }
                }
                if hex.is_empty() {
                    return Err(LexError {
                        message: "empty hex literal".into(),
                        position: start,
                    });
                }
                Ok(Some(Token::HexLiteral(hex)))
            }
            Some(b'b') | Some(b'B') => {
                self.advance();
                let mut bin = String::new();
                while let Some(ch) = self.peek() {
                    if ch == b'0' || ch == b'1' {
                        bin.push(ch as char);
                        self.advance();
                    } else {
                        break;
                    }
                }
                if bin.is_empty() {
                    return Err(LexError {
                        message: "empty binary literal".into(),
                        position: start,
                    });
                }
                Ok(Some(Token::BinLiteral(bin)))
            }
            _ => Err(LexError {
                message: "expected 'x' or 'b' after '#'".into(),
                position: start,
            }),
        }
    }

    fn read_keyword(&mut self) -> Result<Option<Token>, LexError> {
        self.advance(); // skip :
        let mut kw = String::new();
        while let Some(ch) = self.peek() {
            if Self::is_symbol_char(ch) {
                kw.push(ch as char);
                self.advance();
            } else {
                break;
            }
        }
        Ok(Some(Token::Keyword(kw)))
    }

    fn read_quoted_symbol(&mut self) -> Result<Option<Token>, LexError> {
        self.advance(); // skip |
        let mut s = String::new();
        loop {
            match self.advance() {
                None => {
                    return Err(LexError {
                        message: "unterminated quoted symbol".into(),
                        position: self.pos,
                    })
                }
                Some(b'|') => return Ok(Some(Token::Symbol(s))),
                Some(ch) => s.push(ch as char),
            }
        }
    }

    fn read_numeral(&mut self) -> Result<Option<Token>, LexError> {
        let mut num = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                num.push(ch as char);
                self.advance();
            } else {
                break;
            }
        }
        Ok(Some(Token::Numeral(num)))
    }

    fn read_symbol(&mut self) -> Result<Option<Token>, LexError> {
        let mut sym = String::new();
        while let Some(ch) = self.peek() {
            if Self::is_symbol_char(ch) {
                sym.push(ch as char);
                self.advance();
            } else {
                break;
            }
        }
        Ok(Some(Token::Symbol(sym)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_tokens() {
        let mut lexer = Lexer::new("(check-sat)");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![Token::LParen, Token::Symbol("check-sat".into()), Token::RParen]
        );
    }

    #[test]
    fn test_hex_and_bin_literals() {
        let mut lexer = Lexer::new("#xFF #b1010");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![Token::HexLiteral("FF".into()), Token::BinLiteral("1010".into())]
        );
    }

    #[test]
    fn test_comments() {
        let mut lexer = Lexer::new("; this is a comment\n(exit)");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![Token::LParen, Token::Symbol("exit".into()), Token::RParen]
        );
    }

    #[test]
    fn test_keywords() {
        let mut lexer = Lexer::new(":named :status");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![Token::Keyword("named".into()), Token::Keyword("status".into())]
        );
    }

    #[test]
    fn test_string_literal() {
        let mut lexer = Lexer::new("\"hello world\"");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(tokens, vec![Token::StringLiteral("hello world".into())]);
    }

    #[test]
    fn test_declare_fun() {
        let mut lexer = Lexer::new("(declare-fun x () Bool)");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::LParen,
                Token::Symbol("declare-fun".into()),
                Token::Symbol("x".into()),
                Token::LParen,
                Token::RParen,
                Token::Symbol("Bool".into()),
                Token::RParen,
            ]
        );
    }

    #[test]
    fn test_bitvector_index() {
        let mut lexer = Lexer::new("(_ BitVec 32)");
        let tokens = lexer.tokenize().unwrap();
        assert_eq!(
            tokens,
            vec![
                Token::LParen,
                Token::Symbol("_".into()),
                Token::Symbol("BitVec".into()),
                Token::Numeral("32".into()),
                Token::RParen,
            ]
        );
    }
}

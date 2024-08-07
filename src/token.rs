use std::{
    error::Error,
    fmt::{Display, Formatter},
};

#[derive(Debug, PartialEq, Eq)]
pub enum TokenType {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    EOF,
}

impl TokenType {
    pub fn display_name(&self) -> &str {
        match self {
            TokenType::LeftParen => "LEFT_PAREN",
            TokenType::RightParen => "RIGHT_PAREN",
            TokenType::LeftBrace => "LEFT_BRACE",
            TokenType::RightBrace => "RIGHT_BRACE",
            TokenType::EOF => "EOF",
        }
    }
}

impl Display for TokenType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

#[derive(Debug)]
pub struct Token {
    pub kind: TokenType,
    pub lexeme: String,
    pub line: usize,
    pub column: usize,
}

impl Token {
    pub fn new(kind: TokenType, lexeme: String, line: usize, column: usize) -> Self {
        Self {
            kind,
            lexeme,
            line,
            column,
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} null", self.kind.display_name(), self.lexeme)
    }
}

#[derive(Debug)]
pub struct TokenError {
    pub error: TokenErrorType,
    pub line: usize,
    pub column: usize,
}

impl TokenError {
    pub fn new(error: TokenErrorType, line: usize, column: usize) -> Self {
        TokenError {
            error,
            line,
            column,
        }
    }
}

impl Display for TokenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[line {} col {}] Error: {}",
            self.line, self.column, self.error
        )
    }
}

impl Error for TokenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.error)
    }
}

#[derive(thiserror::Error, Debug)]
pub enum TokenErrorType {
    #[error("Unexpected token \"{0}\"")]
    UnexpectedToken(String),
}

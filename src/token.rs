use std::{
    error::Error,
    fmt::{Display, Formatter},
};

#[derive(Debug, PartialEq, Eq)]
pub enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Star,
    Semicolon,

    // One or two character tokens.
    Equal,
    EqualEqual,
    Bang,
    BangEqual,

    EOF,
}

impl TokenType {
    pub fn display_name(&self) -> &str {
        match self {
            TokenType::LeftParen => "LEFT_PAREN",
            TokenType::RightParen => "RIGHT_PAREN",
            TokenType::LeftBrace => "LEFT_BRACE",
            TokenType::RightBrace => "RIGHT_BRACE",
            TokenType::Comma => "COMMA",
            TokenType::Dot => "DOT",
            TokenType::Minus => "MINUS",
            TokenType::Plus => "PLUS",
            TokenType::Star => "STAR",
            TokenType::Semicolon => "SEMICOLON",
            TokenType::Equal => "EQUAL",
            TokenType::EqualEqual => "EQUAL_EQUAL",
            TokenType::Bang => "BANG",
            TokenType::BangEqual => "BANG_EQUAL",
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
        write!(f, "[line {}] Error: {}", self.line, self.error)
    }
}

impl Error for TokenError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.error)
    }
}

#[derive(thiserror::Error, Debug)]
pub enum TokenErrorType {
    #[error("Unexpected character: {0}")]
    UnexpectedToken(String),
}

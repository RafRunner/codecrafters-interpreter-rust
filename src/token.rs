use std::{
    error::Error,
    fmt::{Display, Formatter},
};

use crate::ast::{BinaryOperator, UnaryOperator};

#[derive(Debug, PartialEq, Clone)]
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
    Slash,

    // One or two character tokens.
    Equal,
    EqualEqual,
    Bang,
    BangEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,

    // Literals.
    String(String),
    Number(f64),

    Identifier,

    // Reserved words
    And,
    Class,
    Else,
    False,
    For,
    Fun,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

impl TokenType {
    fn props(&self) -> (&str, Option<BinaryOperator>, Option<UnaryOperator>) {
        match self {
            Self::LeftParen => ("LEFT_PAREN", None, None),
            Self::RightParen => ("RIGHT_PAREN", None, None),
            Self::LeftBrace => ("LEFT_BRACE", None, None),
            Self::RightBrace => ("RIGHT_BRACE", None, None),
            Self::Comma => ("COMMA", None, None),
            Self::Dot => ("DOT", None, None),
            Self::Minus => (
                "MINUS",
                Some(BinaryOperator::Minus),
                Some(UnaryOperator::Negative),
            ),
            Self::Plus => ("PLUS", Some(BinaryOperator::Plus), None),
            Self::Star => ("STAR", Some(BinaryOperator::Times), None),
            Self::Semicolon => ("SEMICOLON", None, None),
            Self::Slash => ("SLASH", Some(BinaryOperator::Divide), None),
            Self::Equal => ("EQUAL", None, None),
            Self::EqualEqual => ("EQUAL_EQUAL", Some(BinaryOperator::Equals), None),
            Self::Bang => ("BANG", None, Some(UnaryOperator::Negation)),
            Self::BangEqual => ("BANG_EQUAL", Some(BinaryOperator::NotEquals), None),
            Self::Less => ("LESS", Some(BinaryOperator::Less), None),
            Self::LessEqual => ("LESS_EQUAL", Some(BinaryOperator::LessEqual), None),
            Self::Greater => ("GREATER", Some(BinaryOperator::Greater), None),
            Self::GreaterEqual => ("GREATER_EQUAL", Some(BinaryOperator::GreaterEqual), None),
            Self::String(..) => ("STRING", None, None),
            Self::Number(..) => ("NUMBER", None, None),
            Self::Identifier => ("IDENTIFIER", None, None),
            Self::And => ("AND", Some(BinaryOperator::LogicAnd), None),
            Self::Class => ("CLASS", None, None),
            Self::Else => ("ELSE", None, None),
            Self::False => ("FALSE", None, None),
            Self::For => ("FOR", None, None),
            Self::Fun => ("FUN", None, None),
            Self::If => ("IF", None, None),
            Self::Nil => ("NIL", None, None),
            Self::Or => ("OR", Some(BinaryOperator::LogicOr), None),
            Self::Print => ("PRINT", None, None),
            Self::Return => ("RETURN", None, None),
            Self::Super => ("SUPER", None, None),
            Self::This => ("THIS", None, None),
            Self::True => ("TRUE", None, None),
            Self::Var => ("VAR", None, None),
            Self::While => ("WHILE", None, None),
        }
    }

    pub fn display_name(&self) -> &str {
        self.props().0
    }

    pub fn binary_operator(&self) -> Option<BinaryOperator> {
        self.props().1
    }

    pub fn unary_operator(&self) -> Option<UnaryOperator> {
        self.props().2
    }

    pub fn check_reserved_word(lexeme: &str) -> Option<Self> {
        match lexeme {
            "and" => Some(Self::And),
            "class" => Some(Self::Class),
            "else" => Some(Self::Else),
            "false" => Some(Self::False),
            "for" => Some(Self::For),
            "fun" => Some(Self::Fun),
            "if" => Some(Self::If),
            "nil" => Some(Self::Nil),
            "or" => Some(Self::Or),
            "print" => Some(Self::Print),
            "return" => Some(Self::Return),
            "super" => Some(Self::Super),
            "this" => Some(Self::This),
            "true" => Some(Self::True),
            "var" => Some(Self::Var),
            "while" => Some(Self::While),
            _ => None,
        }
    }
}

impl Display for TokenType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub kind: TokenType,
    pub lexeme: String,
    pub line: usize,
    pub column: usize,
}

impl Token {
    pub fn new(kind: TokenType, lexeme: &str, line: usize, column: usize) -> Self {
        Self {
            kind,
            lexeme: lexeme.to_owned(),
            line,
            column,
        }
    }

    pub fn genereted(kind: TokenType, lexeme: &str) -> Self {
        Self::new(kind, lexeme, 0, 0)
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let literal = match &self.kind {
            TokenType::String(s) => s.clone(),
            TokenType::Number(n) => format!("{:?}", n),
            _ => "null".to_owned(),
        };

        write!(
            f,
            "{} {} {}",
            self.kind.display_name(),
            self.lexeme,
            literal
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
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

#[derive(thiserror::Error, Debug, PartialEq, Clone)]
pub enum TokenErrorType {
    #[error("Unexpected character: {0}")]
    UnexpectedToken(String),

    #[error("Unterminated string.")]
    UnterminatedString,
}

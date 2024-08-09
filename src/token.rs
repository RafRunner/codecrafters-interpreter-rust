use std::{
    error::Error,
    fmt::{Display, Formatter},
};

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
    pub fn display_name(&self) -> &str {
        match self {
            Self::LeftParen => "LEFT_PAREN",
            Self::RightParen => "RIGHT_PAREN",
            Self::LeftBrace => "LEFT_BRACE",
            Self::RightBrace => "RIGHT_BRACE",
            Self::Comma => "COMMA",
            Self::Dot => "DOT",
            Self::Minus => "MINUS",
            Self::Plus => "PLUS",
            Self::Star => "STAR",
            Self::Semicolon => "SEMICOLON",
            Self::Slash => "SLASH",
            Self::Equal => "EQUAL",
            Self::EqualEqual => "EQUAL_EQUAL",
            Self::Bang => "BANG",
            Self::BangEqual => "BANG_EQUAL",
            Self::Less => "LESS",
            Self::LessEqual => "LESS_EQUAL",
            Self::Greater => "GREATER",
            Self::GreaterEqual => "GREATER_EQUAL",
            Self::String(..) => "STRING",
            Self::Number(..) => "NUMBER",
            Self::Identifier => "IDENTIFIER",
            Self::And => "AND",
            Self::Class => "CLASS",
            Self::Else => "ELSE",
            Self::False => "FALSE",
            Self::For => "FOR",
            Self::Fun => "FUN",
            Self::If => "IF",
            Self::Nil => "NIL",
            Self::Or => "OR",
            Self::Print => "PRINT",
            Self::Return => "RETURN",
            Self::Super => "SUPER",
            Self::This => "THIS",
            Self::True => "TRUE",
            Self::Var => "VAR",
            Self::While => "WHILE",
        }
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
            lexeme: String::from(lexeme),
            line,
            column,
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let literal = match &self.kind {
            TokenType::String(s) => s.clone(),
            TokenType::Number(n) => format!("{:?}", n),
            _ => String::from("null"),
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

#[derive(Debug, PartialEq)]
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

#[derive(thiserror::Error, Debug, PartialEq)]
pub enum TokenErrorType {
    #[error("Unexpected character: {0}")]
    UnexpectedToken(String),

    #[error("Unterminated string.")]
    UnterminatedString,
}

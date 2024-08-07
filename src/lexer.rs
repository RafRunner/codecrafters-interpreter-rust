use std::{iter::Peekable, str::Chars};

use crate::token::{Token, TokenError, TokenErrorType, TokenType};

pub struct Lexer<'a> {
    source_code: &'a str,
}

impl<'a> Lexer<'a> {
    pub fn new(source_code: &'a str) -> Self {
        Self { source_code }
    }

    pub fn iter(&self) -> LexerIterator<'a> {
        LexerIterator {
            chars: self.source_code.chars().peekable(),
            finished: false,
            line: 1,
            column: 0,
        }
    }
}

pub struct LexerIterator<'a> {
    chars: Peekable<Chars<'a>>,
    finished: bool,
    line: usize,
    column: usize,
}

impl<'a> LexerIterator<'a> {
    fn next_char(&mut self) -> Option<char> {
        let next = self.chars.next();

        if let Some(c) = next {
            if c == '\n' {
                self.line += 1;
                self.column = 0;
            } else {
                self.column += 1;
            }
        }

        next
    }

    fn report_error(&self, error: TokenErrorType) -> TokenError {
        TokenError::new(error, self.line, self.column)
    }

    fn parse_token(&mut self, first: char) -> Result<Token, TokenError> {
        let (start_line, start_col) = (self.line, self.column);
        let mut lexeme = first.to_string();

        let kind = match first {
            '(' => TokenType::LeftParen,
            ')' => TokenType::RightParen,
            '{' => TokenType::LeftBrace,
            '}' => TokenType::RightBrace,
            ',' => TokenType::Comma,
            '.' => TokenType::Dot,
            '-' => TokenType::Minus,
            '+' => TokenType::Plus,
            ';' => TokenType::Semicolon,
            '*' => TokenType::Star,

            '=' => {
                if let Some('=') = self.chars.peek() {
                    lexeme.extend(self.next_char());
                    TokenType::EqualEqual
                } else {
                    TokenType::Equal
                }
            }

            _ => return Err(self.report_error(TokenErrorType::UnexpectedToken(lexeme.clone()))),
        };

        Ok(Token::new(kind, lexeme, start_line, start_col))
    }
}

impl<'a> Iterator for LexerIterator<'a> {
    type Item = Result<Token, TokenError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        // Ignoring whitespace
        while let Some(peek) = self.chars.peek() {
            if peek.is_whitespace() {
                self.next_char();
            } else {
                break;
            }
        }

        let token = if let Some(next) = self.next_char() {
            self.parse_token(next)
        } else {
            self.finished = true;
            Ok(Token::new(
                TokenType::EOF,
                String::new(),
                self.line,
                self.column,
            ))
        };

        Some(token)
    }
}

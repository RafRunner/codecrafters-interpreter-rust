use std::{iter::Peekable, str::Chars};

use crate::token::{Token, TokenType};

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
    // source_code: &'a str,
    chars: Peekable<Chars<'a>>,
    finished: bool,
    line: usize,
    column: usize,
}

impl<'a> LexerIterator<'a> {
    fn update_position(&mut self, c: char) {
        if c == '\n' {
            self.line += 1;
            self.column = 0;
        } else {
            self.column += 1;
        }
    }

    fn next_char(&mut self) -> Option<char> {
        let next = self.chars.next();

        if let Some(c) = next {
            self.update_position(c)
        }

        next
    }
}

impl<'a> Iterator for LexerIterator<'a> {
    type Item = Result<Token, String>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        // Ignoring whitespace
        while let Some(next) = self.chars.peek().cloned() {
            if next.is_whitespace() {
                self.next_char();
            } else {
                break;
            }
        }

        let token = if let Some(next) = self.next_char() {
            let lexeme = next.to_string();
            let next_token = match next {
                '(' => Ok(TokenType::LeftParen),
                ')' => Ok(TokenType::RightParen),
                _ => Err(format!("Invalid token at line {}, column {}: {}", self.line, self.column, next)),
            };

            next_token.map(|kind| Token::new(kind, lexeme, self.line, self.column))
        } else {
            self.finished = true;
            Ok(Token::new(TokenType::EOF, String::new(), self.line, self.column))
        };

        Some(token)
    }
}

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

        let token = if let Some(first) = self.next_char() {
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
                '!' => {
                    if let Some('=') = self.chars.peek() {
                        lexeme.extend(self.next_char());
                        TokenType::BangEqual
                    } else {
                        TokenType::Bang
                    }
                }
                '<' => {
                    if let Some('=') = self.chars.peek() {
                        lexeme.extend(self.next_char());
                        TokenType::LessEqual
                    } else {
                        TokenType::Less
                    }
                }
                '>' => {
                    if let Some('=') = self.chars.peek() {
                        lexeme.extend(self.next_char());
                        TokenType::GreaterEqual
                    } else {
                        TokenType::Greater
                    }
                }
                '/' => {
                    // Ignoring comments
                    if let Some('/') = self.chars.peek() {
                        while let Some(c) = self.next_char() {
                            if c == '\n' {
                                break;
                            }
                        }

                        return self.next();
                    } else {
                        TokenType::Slash
                    }
                }

                _ => {
                    return Some(Err(TokenError::new(
                        TokenErrorType::UnexpectedToken(lexeme.clone()),
                        start_line,
                        start_col,
                    )))
                }
            };

            Ok(Token::new(kind, lexeme, start_line, start_col))
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

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

    fn if_match(
        &mut self,
        test: char,
        lexeme: &mut String,
        success: TokenType,
        fail: TokenType,
    ) -> TokenType {
        if self.chars.peek().map(|&c| c == test).unwrap_or(false) {
            lexeme.extend(self.next_char());
            success
        } else {
            fail
        }
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

                '=' => self.if_match('=', &mut lexeme, TokenType::EqualEqual, TokenType::Equal),
                '!' => self.if_match('=', &mut lexeme, TokenType::BangEqual, TokenType::Bang),
                '<' => self.if_match('=', &mut lexeme, TokenType::LessEqual, TokenType::Less),
                '>' => self.if_match(
                    '=',
                    &mut lexeme,
                    TokenType::GreaterEqual,
                    TokenType::Greater,
                ),
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

                '"' => {
                    while let Some(c) = self.next_char() {
                        lexeme.push(c);
                        if c == '"' {
                            break;
                        }
                    }

                    if !lexeme.ends_with('"') || lexeme.len() < 2 {
                        return Some(Err(TokenError::new(
                            TokenErrorType::UnterminatedString,
                            start_line,
                            start_col,
                        )));
                    } else {
                        TokenType::String(lexeme[1..lexeme.len() - 1].to_string())
                    }
                }
                c if c.is_ascii_digit() => {
                    while let Some(c) = self.chars.peek() {
                        if c.is_ascii_digit() {
                            lexeme.extend(self.next_char());
                        } else if *c == '.' {
                            if self
                                .chars
                                .clone()
                                .nth(2)
                                .map(|c| c.is_ascii_digit())
                                .unwrap_or(false)
                            {
                                // Consume the "."
                                lexeme.extend(self.next_char());

                                while let Some(c) = self.chars.peek() {
                                    if c.is_ascii_digit() {
                                        lexeme.extend(self.next_char())
                                    } else {
                                        break;
                                    }
                                }
                            }

                            break;
                        } else {
                            break;
                        }
                    }

                    TokenType::Number(lexeme.parse().expect("lexeme should be a valid number"))
                }
                c if c.is_ascii_alphabetic() || c == '_' => {
                    while let Some(c) = self.chars.peek() {
                        if c.is_ascii_alphanumeric() || *c == '_' {
                            lexeme.extend(self.next_char())
                        } else {
                            break;
                        }
                    }
                    
                    TokenType::Identifier
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

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
            lexeme: String::new(),
            finished: false,
            line: 1,
            column: 0,
        }
    }
}

pub struct LexerIterator<'a> {
    chars: Peekable<Chars<'a>>,
    lexeme: String,
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

    fn if_next(&mut self, test: char, success: TokenType, fail: TokenType) -> TokenType {
        if self.chars.peek().map_or(false, |&c| c == test) {
            self.consume_char();
            success
        } else {
            fail
        }
    }

    fn consume_char(&mut self) {
        if let Some(next) = self.next_char() {
            self.lexeme.push(next);
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
            self.lexeme = first.to_string();

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

                '=' => self.if_next('=', TokenType::EqualEqual, TokenType::Equal),
                '!' => self.if_next('=', TokenType::BangEqual, TokenType::Bang),
                '<' => self.if_next('=', TokenType::LessEqual, TokenType::Less),
                '>' => self.if_next('=', TokenType::GreaterEqual, TokenType::Greater),
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
                        self.lexeme.push(c);
                        if c == '"' {
                            break;
                        }
                    }

                    if !self.lexeme.ends_with('"') || self.lexeme.len() < 2 {
                        return Some(Err(TokenError::new(
                            TokenErrorType::UnterminatedString,
                            start_line,
                            start_col,
                        )));
                    } else {
                        TokenType::String(self.lexeme[1..self.lexeme.len() - 1].to_string())
                    }
                }
                c if c.is_ascii_digit() => {
                    while let Some(c) = self.chars.peek() {
                        if c.is_ascii_digit() {
                            self.consume_char();
                        } else if *c == '.' {
                            if self
                                .chars
                                .clone()
                                .nth(1)
                                .map_or(false, |c| c.is_ascii_digit())
                            {
                                // Consume the "."
                                self.consume_char();

                                while let Some(c) = self.chars.peek() {
                                    if c.is_ascii_digit() {
                                        self.consume_char();
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

                    TokenType::Number(
                        self.lexeme
                            .parse()
                            .expect("lexeme should be a valid number"),
                    )
                }
                c if c.is_ascii_alphabetic() || c == '_' => {
                    while let Some(c) = self.chars.peek() {
                        if c.is_ascii_alphanumeric() || *c == '_' {
                            self.consume_char();
                        } else {
                            break;
                        }
                    }

                    TokenType::check_reserved_word(&self.lexeme).unwrap_or(TokenType::Identifier)
                }

                _ => {
                    return Some(Err(TokenError::new(
                        TokenErrorType::UnexpectedToken(self.lexeme.clone()),
                        start_line,
                        start_col,
                    )))
                }
            };

            Ok(Token::new(kind, &self.lexeme, start_line, start_col))
        } else {
            self.finished = true;
            Ok(Token::new(TokenType::EOF, "", self.line, self.column + 1))
        };

        Some(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_lexer(input: &str) -> Vec<Result<Token, TokenError>> {
        Lexer::new(input).iter().collect()
    }

    fn test_lexer_no_errors(input: &str) -> Vec<Token> {
        Lexer::new(input)
            .iter()
            .map(|res| match res {
                Ok(tok) => tok,
                Err(e) => panic!("Parsing error: {}", e),
            })
            .collect()
    }

    fn assert_single_token(input: &str, expected: TokenType) {
        let tokens = test_lexer_no_errors(input);

        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].kind, expected);
    }

    #[test]
    fn test_single_character_tokens() {
        let source = "(){},.-+*;";
        let tokens = test_lexer_no_errors(source);

        assert_eq!(tokens.len(), 11);
        assert_eq!(tokens[0], Token::new(TokenType::LeftParen, "(", 1, 1));
        assert_eq!(tokens[1], Token::new(TokenType::RightParen, ")", 1, 2));
        assert_eq!(tokens[2], Token::new(TokenType::LeftBrace, "{", 1, 3));
        assert_eq!(tokens[3], Token::new(TokenType::RightBrace, "}", 1, 4));
        assert_eq!(tokens[4], Token::new(TokenType::Comma, ",", 1, 5));
        assert_eq!(tokens[5], Token::new(TokenType::Dot, ".", 1, 6));
        assert_eq!(tokens[6], Token::new(TokenType::Minus, "-", 1, 7));
        assert_eq!(tokens[7], Token::new(TokenType::Plus, "+", 1, 8));
        assert_eq!(tokens[8], Token::new(TokenType::Star, "*", 1, 9));
        assert_eq!(tokens[9], Token::new(TokenType::Semicolon, ";", 1, 10));
        assert_eq!(tokens[10], Token::new(TokenType::EOF, "", 1, 11));
    }

    #[test]
    fn test_two_character_tokens() {
        let source = "=== !=\n<= >=\n";
        let tokens = test_lexer_no_errors(source);

        assert_eq!(tokens.len(), 6);
        assert_eq!(tokens[0], Token::new(TokenType::EqualEqual, "==", 1, 1));
        assert_eq!(tokens[1], Token::new(TokenType::Equal, "=", 1, 3));
        assert_eq!(tokens[2], Token::new(TokenType::BangEqual, "!=", 1, 5));
        assert_eq!(tokens[3], Token::new(TokenType::LessEqual, "<=", 2, 1));
        assert_eq!(tokens[4], Token::new(TokenType::GreaterEqual, ">=", 2, 4));
        assert_eq!(tokens[5], Token::new(TokenType::EOF, "", 3, 1));
    }

    #[test]
    fn test_strings() {
        let source = "\"hello\"name=\"world\"";
        let tokens = test_lexer_no_errors(source);

        assert_eq!(tokens.len(), 5);
        assert_eq!(
            tokens[0],
            Token::new(TokenType::String("hello".to_string()), "\"hello\"", 1, 1)
        );
        assert_eq!(tokens[1], Token::new(TokenType::Identifier, "name", 1, 8));
        assert_eq!(tokens[2], Token::new(TokenType::Equal, "=", 1, 12));
        assert_eq!(
            tokens[3],
            Token::new(TokenType::String("world".to_string()), "\"world\"", 1, 13)
        );
        assert_eq!(tokens[4], Token::new(TokenType::EOF, "", 1, 20));
    }

    #[test]
    fn test_numbers() {
        let source = "123 2.0 456.789+12.34.56";
        let tokens = test_lexer_no_errors(source);

        assert_eq!(tokens.len(), 8);
        assert_eq!(tokens[0], Token::new(TokenType::Number(123.0), "123", 1, 1));
        assert_eq!(tokens[1], Token::new(TokenType::Number(2.0), "2.0", 1, 5));
        assert_eq!(
            tokens[2],
            Token::new(TokenType::Number(456.789), "456.789", 1, 9)
        );
        assert_eq!(tokens[3], Token::new(TokenType::Plus, "+", 1, 16));
        assert_eq!(
            tokens[4],
            Token::new(TokenType::Number(12.34), "12.34", 1, 17)
        );
        assert_eq!(tokens[5], Token::new(TokenType::Dot, ".", 1, 22));
        assert_eq!(tokens[6], Token::new(TokenType::Number(56.0), "56", 1, 23));
        assert_eq!(tokens[7], Token::new(TokenType::EOF, "", 1, 25));
    }

    #[test]
    fn test_comments() {
        let source = "\"Olá\" // This is a comment\n123";
        let tokens = test_lexer_no_errors(source);

        assert_eq!(tokens.len(), 3);
        assert_eq!(
            tokens[0],
            Token::new(TokenType::String("Olá".to_string()), "\"Olá\"", 1, 1)
        );
        assert_eq!(tokens[1], Token::new(TokenType::Number(123.0), "123", 2, 1));
        assert_eq!(tokens[2], Token::new(TokenType::EOF, "", 2, 4));
    }

    #[test]
    fn test_unterminated_string() {
        let source = "\"This is an unterminated string";
        let tokens = test_lexer(source);

        assert_eq!(tokens.len(), 2);
        assert_eq!(
            tokens[0],
            Err(TokenError::new(TokenErrorType::UnterminatedString, 1, 1))
        );
        assert_eq!(tokens[1], Ok(Token::new(TokenType::EOF, "", 1, 32)));
    }

    #[test]
    fn test_unexpected_character() {
        let source = "§+orchid";
        let tokens = test_lexer(source);

        assert_eq!(tokens.len(), 4);
        assert_eq!(
            tokens[0],
            Err(TokenError::new(
                TokenErrorType::UnexpectedToken("§".to_string()),
                1,
                1
            ))
        );
        assert_eq!(tokens[1], Ok(Token::new(TokenType::Plus, "+", 1, 2)));
        assert_eq!(
            tokens[2],
            Ok(Token::new(TokenType::Identifier, "orchid", 1, 3))
        );
        assert_eq!(tokens[3], Ok(Token::new(TokenType::EOF, "", 1, 9)));
    }

    #[test]
    fn test_reserved_words() {
        assert_single_token("\tand", TokenType::And);
        assert_single_token("class", TokenType::Class);
        assert_single_token("\nelse", TokenType::Else);
        assert_single_token("false", TokenType::False);
        assert_single_token("for\n", TokenType::For);
        assert_single_token("fun\t", TokenType::Fun);
        assert_single_token("if", TokenType::If);
        assert_single_token("nil", TokenType::Nil);
        assert_single_token("or", TokenType::Or);
        assert_single_token("print ", TokenType::Print);
        assert_single_token("  return", TokenType::Return);
        assert_single_token("super", TokenType::Super);
        assert_single_token("this", TokenType::This);
        assert_single_token("true  ", TokenType::True);
        assert_single_token("var", TokenType::Var);
        assert_single_token(" while", TokenType::While);
    }

    #[test]
    fn edge_cases() {
        let source = "andor 3.\nprint -2.abs();\n";
        let tokens = test_lexer_no_errors(source);

        assert_eq!(tokens.len(), 12);
        assert_eq!(tokens[0], Token::new(TokenType::Identifier, "andor", 1, 1));
        assert_eq!(tokens[1], Token::new(TokenType::Number(3.0), "3", 1, 7));
        assert_eq!(tokens[2], Token::new(TokenType::Dot, ".", 1, 8));
        assert_eq!(tokens[3], Token::new(TokenType::Print, "print", 2, 1));
        assert_eq!(tokens[4], Token::new(TokenType::Minus, "-", 2, 7));
        assert_eq!(tokens[5], Token::new(TokenType::Number(2.0), "2", 2, 8));
        assert_eq!(tokens[6], Token::new(TokenType::Dot, ".", 2, 9));
        assert_eq!(tokens[7], Token::new(TokenType::Identifier, "abs", 2, 10));
        assert_eq!(tokens[8], Token::new(TokenType::LeftParen, "(", 2, 13));
        assert_eq!(tokens[9], Token::new(TokenType::RightParen, ")", 2, 14));
        assert_eq!(tokens[10], Token::new(TokenType::Semicolon, ";", 2, 15));
        assert_eq!(tokens[11], Token::new(TokenType::EOF, "", 3, 1));
    }
}

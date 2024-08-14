use std::{
    error::Error,
    fmt::{Display, Formatter},
    iter::Peekable,
};

use crate::{
    ast::{Expression, ExpressionType, LiteralExpression, Program, Statement, StatementType},
    lexer::{Lexer, LexerIterator},
    token::{Token, TokenError, TokenType},
};

pub fn parse_program(input: &str) -> Result<Program, ParserError> {
    let lexer = Lexer::new(input);
    let mut parser = Parser::new(lexer);

    parser.parse_program()
}

/**
 * Lox Grammar so far:
 *
 * expression     → equality ;
 * equality       → comparison ( ( "!=" | "==" ) comparison )* ;
 * comparison     → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
 * term           → factor ( ( "-" | "+" ) factor )* ;
 * factor         → unary ( ( "/" | "*" ) unary )* ;
 * unary          → ( "!" | "-" ) unary
 *                | primary ;
 * primary        → NUMBER | STRING | "true" | "false" | "nil"
 *                | "(" expression ")" ;
 */

pub struct Parser<'a> {
    lexer: Peekable<LexerIterator<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer: lexer.iter().peekable(),
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, ParserError> {
        let mut program = Program::new();

        while let Some(result) = self.lexer.next() {
            let statement = match result {
                Ok(token) => self.parse_statement(token),
                Err(e) => {
                    let (line, col) = (e.line, e.column);
                    Err(ParserError::new(
                        ParserErrorType::TokenError { error: e },
                        line,
                        col,
                    ))
                }
            }?;
            program.statements.push(statement);
        }

        Ok(program)
    }

    fn parse_statement(&mut self, token: Token) -> Result<Statement, ParserError> {
        let expression = self.parse_expression(token.clone())?;

        Ok(Statement::new(
            token,
            StatementType::Expression { expr: expression },
        ))
    }

    fn parse_expression(&mut self, token: Token) -> Result<Expression, ParserError> {
        self.parse_equality(token.clone())
    }

    fn parse_equality(&mut self, token: Token) -> Result<Expression, ParserError> {
        self.parse_binary_operation(
            token,
            Self::parse_comparison,
            &[TokenType::EqualEqual, TokenType::BangEqual],
        )
    }

    fn parse_comparison(&mut self, token: Token) -> Result<Expression, ParserError> {
        self.parse_binary_operation(
            token,
            Self::parse_term,
            &[
                TokenType::Greater,
                TokenType::GreaterEqual,
                TokenType::Less,
                TokenType::LessEqual,
            ],
        )
    }

    fn parse_term(&mut self, token: Token) -> Result<Expression, ParserError> {
        self.parse_binary_operation(
            token,
            Self::parse_factor,
            &[TokenType::Plus, TokenType::Minus],
        )
    }

    fn parse_factor(&mut self, token: Token) -> Result<Expression, ParserError> {
        self.parse_binary_operation(
            token,
            Self::parse_unary,
            &[TokenType::Star, TokenType::Slash],
        )
    }

    fn parse_unary(&mut self, token: Token) -> Result<Expression, ParserError> {
        if matches!(token.kind, TokenType::Bang | TokenType::Minus) {
            let operator = token.kind.props().2.unwrap();
            let next_token = self.advance(&token)?;
            let unary = self.parse_unary(next_token)?;

            Ok(Expression::new(
                token,
                ExpressionType::Unary {
                    operator,
                    expr: Box::new(unary),
                },
            ))
        } else {
            self.parse_primary(token)
        }
    }

    fn parse_primary(&mut self, token: Token) -> Result<Expression, ParserError> {
        match &token.kind {
            TokenType::LeftParen => {
                let next_token = self.advance(&token)?;
                let inner = self.parse_expression(next_token)?;

                let closing = self.advance_custom(ParserError::new(
                    ParserErrorType::UnmatchedParenthesis,
                    inner.token.line,
                    inner.token.column,
                ))?;
                if closing.kind == TokenType::RightParen {
                    Ok(Expression::new(
                        token,
                        ExpressionType::Grouping {
                            expr: Box::new(inner),
                        },
                    ))
                } else {
                    Err(ParserError::new(
                        ParserErrorType::UnmatchedParenthesis,
                        inner.token.line,
                        inner.token.column,
                    ))
                }
            }
            TokenType::True => Ok(Expression::literal(token, LiteralExpression::True)),
            TokenType::False => Ok(Expression::literal(token, LiteralExpression::False)),
            TokenType::Nil => Ok(Expression::literal(token, LiteralExpression::Nil)),
            TokenType::String(s) => {
                let s = s.clone();
                Ok(Expression::literal(token, LiteralExpression::String(s)))
            }
            TokenType::Number(n) => {
                let n = *n;
                Ok(Expression::literal(token, LiteralExpression::Number(n)))
            }
            _ => Err(ParserError::new(
                ParserErrorType::UnexpectedToken {
                    token: token.lexeme,
                },
                token.line,
                token.column,
            )),
        }
    }

    // Helper functions

    fn parse_binary_operation<F>(
        &mut self,
        token: Token,
        parse_lower: F,
        operators: &[TokenType],
    ) -> Result<Expression, ParserError>
    where
        F: Fn(&mut Self, Token) -> Result<Expression, ParserError>,
    {
        let mut left = parse_lower(self, token)?;

        while let Some(Ok(tok)) = self.lexer.peek() {
            if operators.contains(&tok.kind) {
                let operation = self.lexer.next().unwrap().unwrap();
                let operator = operation.kind.props().1.unwrap();
                let right = self
                    .advance(&operation)
                    .and_then(|next_token| parse_lower(self, next_token))?;

                left = Expression::new(
                    operation,
                    ExpressionType::Binary {
                        left: Box::new(left),
                        operator,
                        rigth: Box::new(right),
                    },
                );
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn advance(&mut self, prev_token: &Token) -> Result<Token, ParserError> {
        self.advance_custom(ParserError::new(
            ParserErrorType::UnexpectedEof,
            prev_token.line,
            prev_token.column,
        ))
    }

    fn advance_custom(&mut self, error: ParserError) -> Result<Token, ParserError> {
        match self.lexer.next() {
            Some(result) => result.map_err(|e| {
                let (line, col) = (e.line, e.column);
                ParserError::new(ParserErrorType::TokenError { error: e }, line, col)
            }),
            None => Err(error),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct ParserError {
    pub error: ParserErrorType,
    pub line: usize,
    pub column: usize,
}

impl ParserError {
    pub fn new(error: ParserErrorType, line: usize, column: usize) -> Self {
        Self {
            error,
            line,
            column,
        }
    }
}

impl Display for ParserError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let ParserErrorType::TokenError { error } = &self.error {
            write!(f, "{}", error)
        } else {
            write!(f, "[line {}] Error: {}", self.line, self.error)
        }
    }
}

impl Error for ParserError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.error)
    }
}

#[derive(Debug, thiserror::Error, PartialEq)]
pub enum ParserErrorType {
    #[error("Unexpected token '{token}'")]
    UnexpectedToken { token: String },

    #[error("Expected closing ')'")]
    UnmatchedParenthesis,

    #[error("{error}")]
    TokenError { error: TokenError },

    #[error("Unexpected end of file")]
    UnexpectedEof,
}

#[cfg(test)]
mod tests {

    fn parse_program(input: &str) -> String {
        let program = super::parse_program(input).expect("Program did not parse correctly");

        program.to_string()
    }

    #[test]
    fn parse_literals() {
        let tests = vec![
            ("23", "23.0"),
            ("\"str\"", "str"),
            ("true", "true"),
            ("false", "false"),
        ];

        for (input, expected) in tests {
            assert_eq!(parse_program(input), expected);
        }
    }

    #[test]
    fn parse_binary_operation() {
        let tests = vec![
            ("32 + 124.32", "(+ 32.0 124.32)"),
            ("nil * true", "(* nil true)"),
            ("4323.0 - 43 + 321", "(+ (- 4323.0 43.0) 321.0)"),
            ("2 + 3 * 5", "(+ 2.0 (* 3.0 5.0))"),
            ("2 + 3 + 1 / 5", "(+ (+ 2.0 3.0) (/ 1.0 5.0))"),
            ("(2 + 3) * 5", "(* (group (+ 2.0 3.0)) 5.0)"),
        ];

        for (input, expected) in tests {
            assert_eq!(parse_program(input), expected);
        }
    }

    #[test]
    fn parse_unary_operations() {
        let tests = vec![
            ("-123", "(- 123.0)"),
            ("!true", "(! true)"),
            ("-false", "(- false)"),
            ("!!true", "(! (! true))"),
            ("- - 5", "(- (- 5.0))"),
            ("-(5 + 3)", "(- (group (+ 5.0 3.0)))"),
        ];

        for (input, expected) in tests {
            assert_eq!(parse_program(input), expected);
        }
    }

    #[test]
    fn parse_complex_expressions() {
        let tests = vec![
            ("-123 * 456 >= 3", "(>= (* (- 123.0) 456.0) 3.0)"),
            ("!true == false", "(== (! true) false)"),
            ("3 * -2 + 4", "(+ (* 3.0 (- 2.0)) 4.0)"),
            (
                "(5 - 3) * -(7 / 2)",
                "(* (group (- 5.0 3.0)) (- (group (/ 7.0 2.0))))",
            ),
            (
                "!!(nil == false) < 0",
                "(< (! (! (group (== nil false)))) 0.0)",
            ),
            (
                "(2 + 3) * -(5 + 1)",
                "(* (group (+ 2.0 3.0)) (- (group (+ 5.0 1.0))))",
            ),
        ];

        for (input, expected) in tests {
            assert_eq!(parse_program(input), expected);
        }
    }

    #[test]
    fn parse_multiple_comparisons() {
        let tests = vec![
            ("-3 > 2", "(> (- 3.0) 2.0)"),
            ("!5 < 4", "(< (! 5.0) 4.0)"),
            ("7 == --7", "(== 7.0 (- (- 7.0)))"),
            ("3 + 2 > 1 + 1", "(> (+ 3.0 2.0) (+ 1.0 1.0))"),
            ("2 * 2 == 4", "(== (* 2.0 2.0) 4.0)"),
            ("3 * (2 + 1) < 10", "(< (* 3.0 (group (+ 2.0 1.0))) 10.0)"),
            ("3 + 2 * 4 == 14", "(== (+ 3.0 (* 2.0 4.0)) 14.0)"),
            (
                "(1 + 2) * 3 > 2 == true",
                "(== (> (* (group (+ 1.0 2.0)) 3.0) 2.0) true)",
            ),
            ("4 / 2 <= 2 == false", "(== (<= (/ 4.0 2.0) 2.0) false)"),
            ("2 < 3 > 1", "(> (< 2.0 3.0) 1.0)"),
            ("1 + 2 == 3 > 0", "(== (+ 1.0 2.0) (> 3.0 0.0))"),
            ("2 * 3 > 5 == 1 < 4", "(== (> (* 2.0 3.0) 5.0) (< 1.0 4.0))"),
        ];

        for (input, expected) in tests {
            assert_eq!(parse_program(input), expected);
        }
    }
}

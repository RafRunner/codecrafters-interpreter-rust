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
        if token.kind == TokenType::LeftParen {
            let next_token = self.advance(&token)?;
            let inner = self.parse_expression(next_token)?;

            let closing = self.advance_message(ParserError::new(
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
        } else {
            let literal = self.parse_literal(token.clone())?;

            Ok(Expression::new(token, ExpressionType::Literal { literal }))
        }
    }

    fn parse_literal(&self, token: Token) -> Result<LiteralExpression, ParserError> {
        match token.kind {
            TokenType::True => Ok(LiteralExpression::True),
            TokenType::False => Ok(LiteralExpression::False),
            TokenType::Nil => Ok(LiteralExpression::Nil),
            TokenType::String(s) => Ok(LiteralExpression::String { literal: s }),
            TokenType::Number(n) => Ok(LiteralExpression::Number { literal: n }),
            _ => Err(ParserError::new(
                ParserErrorType::UnexpectedToken {
                    token: token.lexeme,
                },
                token.line,
                token.column,
            )),
        }
    }

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
        self.advance_message(ParserError::new(
            ParserErrorType::UnexpectedEof,
            prev_token.line,
            prev_token.column,
        ))
    }

    fn advance_message(&mut self, error: ParserError) -> Result<Token, ParserError> {
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

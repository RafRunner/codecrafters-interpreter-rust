use std::iter::Peekable;

use crate::{
    ast::{Expression, ExpressionType, LiteralExpression, Program, Statement, StatementType},
    lexer::{Lexer, LexerIterator},
    token::{Token, TokenType},
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

    pub fn parse_program(&mut self) -> Result<Program, anyhow::Error> {
        let mut program = Program::new();

        while let Some(result) = self.lexer.next() {
            let statement = match result {
                Ok(token) => self.parse_statement(token),
                Err(e) => Err(e.into()),
            }?;
            program.statements.push(statement);
        }

        Ok(program)
    }

    fn parse_statement(&mut self, token: Token) -> Result<Statement, anyhow::Error> {
        let expression = self.parse_expression(token.clone())?;

        Ok(Statement::new(
            token,
            StatementType::Expression { expr: expression },
        ))
    }

    fn parse_expression(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        self.parse_equality(token.clone())
    }

    fn parse_equality(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        let mut left = self.parse_comparison(token.clone())?;

        while let Some(Ok(tok)) = self.lexer.peek() {
            match tok.kind {
                TokenType::Equal | TokenType::BangEqual => {
                    // Checked it existis and is a valid "==" or "!=" token
                    left = self.create_binary_exp(left)?;
                }
                _ => break,
            }
        }

        Ok(left)
    }

    fn parse_comparison(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        let mut left = self.parse_term(token.clone())?;

        while let Some(Ok(tok)) = self.lexer.peek() {
            match tok.kind {
                TokenType::Greater
                | TokenType::GreaterEqual
                | TokenType::Less
                | TokenType::LessEqual => {
                    // Checked it existis and is a valid ">", ">=", "<" or "<=" token
                    left = self.create_binary_exp(left)?;
                }
                _ => break,
            }
        }

        Ok(left)
    }

    fn parse_term(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        let mut left = self.parse_factor(token.clone())?;

        while let Some(Ok(tok)) = self.lexer.peek() {
            match tok.kind {
                TokenType::Plus | TokenType::Minus => {
                    // Checked it existis and is a valid "+" or "-" token
                    left = self.create_binary_exp(left)?;
                }
                _ => break,
            }
        }

        Ok(left)
    }

    fn parse_factor(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        let mut left = self.parse_unary(token.clone())?;

        while let Some(Ok(tok)) = self.lexer.peek() {
            match tok.kind {
                TokenType::Star | TokenType::Slash => {
                    // Checked it existis and is a valid "*" or "/" token
                    left = self.create_binary_exp(left)?;
                }
                _ => break,
            }
        }

        Ok(left)
    }

    fn parse_unary(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        if matches!(token.kind, TokenType::Bang | TokenType::Minus) {
            let operator = token.kind.props().2.unwrap();
            let next_token = self.advance()?;
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

    fn parse_primary(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        if token.kind == TokenType::LeftParen {
            let next_token = self.advance()?;
            let inner = self.parse_expression(next_token)?;

            let closing = self.advance()?;
            if closing.kind == TokenType::RightParen {
                Ok(Expression::new(
                    token,
                    ExpressionType::Grouping {
                        expr: Box::new(inner),
                    },
                ))
            } else {
                Err(anyhow::anyhow!(
                    "Grouping expression needs closing ')' at {:?}",
                    token
                ))
            }
        } else {
            let literal = self.parse_literal(token.clone())?;

            Ok(Expression::new(token, ExpressionType::Literal { literal }))
        }
    }

    fn parse_literal(&self, token: Token) -> Result<LiteralExpression, anyhow::Error> {
        match token.kind {
            TokenType::True => Ok(LiteralExpression::True),
            TokenType::False => Ok(LiteralExpression::False),
            TokenType::Nil => Ok(LiteralExpression::Nil),
            TokenType::String(s) => Ok(LiteralExpression::String { literal: s }),
            TokenType::Number(n) => Ok(LiteralExpression::Number { literal: n }),
            _ => Err(anyhow::anyhow!("Unexpected token at {:?}", token)),
        }
    }

    fn create_binary_exp(&mut self, left: Expression) -> Result<Expression, anyhow::Error> {
        let operation = self
            .lexer
            .next()
            .expect("Compiler bug. Check if next token exists")
            .expect("Compiler Bug. Check if next token is Ok");
        let operator = operation
            .kind
            .props()
            .1
            .expect("Compiler Bug. Check if TokenType has an associated BinaryOperator");
        let next_token = self.advance()?;
        let rigth = self.parse_unary(next_token)?;

        Ok(Expression::new(
            operation,
            ExpressionType::Binary {
                left: Box::new(left),
                operator,
                rigth: Box::new(rigth),
            },
        ))
    }

    fn advance(&mut self) -> Result<Token, anyhow::Error> {
        match self.lexer.next() {
            Some(result) => result.map_err(|e| e.into()),
            None => Err(anyhow::anyhow!("Unexpected expression end")),
        }
    }
}

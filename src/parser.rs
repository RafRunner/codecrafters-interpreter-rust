use std::iter::Peekable;

use crate::{
    ast::{
        BinaryOperator, Expression, ExpressionType, Program, Statement,
        StatementType,
    },
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
                    let operator = if tok.kind == TokenType::Equal {
                        BinaryOperator::Equals
                    } else {
                        BinaryOperator::NotEquals
                    };

                    // Checked it existis and is a valid "==" or "!=" token
                    let operaoperation = self.lexer.next().unwrap().unwrap();
                    let next_token = self.advance()?;
                    let rigth = self.parse_comparison(next_token)?;

                    left = Expression::new(
                        operaoperation,
                        ExpressionType::Binary {
                            left: Box::new(left),
                            operator,
                            rigth: Box::new(rigth),
                        },
                    )
                }
                _ => break,
            }
        }

        Ok(left)
    }

    fn parse_comparison(&mut self, token: Token) -> Result<Expression, anyhow::Error> {
        todo!()
    }

    fn advance(&mut self) -> Result<Token, anyhow::Error> {
        match self.lexer.next() {
            Some(result) => result.map_err(|e| e.into()),
            None => Err(anyhow::anyhow!("Unexpected expression end")),
        }
    }
}

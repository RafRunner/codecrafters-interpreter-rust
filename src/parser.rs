use std::iter::Peekable;

use crate::{
    ast::{Expression, ExpressionType, LiteralExpression, Program, Statement, StatementType},
    lexer::{Lexer, LexerIterator},
    token::{Token, TokenType},
};

pub struct Parser<'a> {
    lexer: Peekable<LexerIterator<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer: lexer.iter().peekable(),
        }
    }

    pub fn parse(&mut self) -> Result<Program, anyhow::Error> {
        let mut program = Program::new();

        while let Some(result) = self.lexer.next() {
            let statement = match result {
                Ok(tok) => match self.statement(tok) {
                    Some(stmt) => stmt,
                    None => break,
                },
                Err(e) => Err(e.into()),
            }?;
            program.statements.push(statement);
        }

        Ok(program)
    }

    fn statement(&self, tok: Token) -> Option<Result<Statement, anyhow::Error>> {
        match tok.kind {
            TokenType::True => Some(Ok(
                self.create_literal_statement(tok, LiteralExpression::True)
            )),
            TokenType::False => Some(Ok(
                self.create_literal_statement(tok, LiteralExpression::False)
            )),
            TokenType::Nil => Some(Ok(
                self.create_literal_statement(tok, LiteralExpression::Nil)
            )),
            TokenType::String(ref s) => Some(Ok(self.create_literal_statement(
                tok.clone(),
                LiteralExpression::String { literal: s.clone() },
            ))),
            TokenType::Number(n) => Some(Ok(
                self.create_literal_statement(tok, LiteralExpression::Number { literal: n })
            )),
            TokenType::EOF => None,
            _ => Some(Err(anyhow::anyhow!("Parser error at {:?}", tok))),
        }
    }

    fn create_literal_statement(&self, token: Token, literal: LiteralExpression) -> Statement {
        Statement {
            token: token.clone(),
            kind: StatementType::Expression {
                expr: Expression {
                    token,
                    kind: ExpressionType::Literal { literal },
                },
            },
        }
    }
}

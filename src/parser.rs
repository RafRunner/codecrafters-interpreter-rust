use std::{
    error::Error,
    fmt::{Display, Formatter},
    iter::Peekable,
};

use crate::{
    ast::{
        AssignmentKind, Expression, ExpressionType, IdentifierStruct, LiteralExpression, Program,
        Statement, StatementType,
    },
    lexer::{Lexer, LexerIterator},
    token::{Token, TokenError, TokenType},
};

#[allow(clippy::result_large_err)]
pub fn parse_program(
    input: &str,
    optional_semi_expressions: bool,
) -> Result<Program, ParserOrTokenError> {
    let lexer = Lexer::new(input);
    let mut parser = Parser::new(lexer, optional_semi_expressions);

    parser.parse_program()
}

/**
 * Lox Grammar so far:
 *
 * program        -> declaration* EOF ;
 *
 * declaration    -> varDecl
 *                 | statement ;
 * varDecl        -> "var" IDENTIFIER ( "=" expression )? ";" ;
 *
 * statement      -> exprStmt
 *                 | ifStmt
 *                 | printStmt
 *                 | whileStmt
 *                 | forStmt
 *                 | blockStmt ;
 * exprStmt       -> expression ";" ;
 * ifStmt         -> "if" "(" expression ")" statement
 *                   ( "else" statement)? ;
 * printStmt      -> "print" expression ";" ;
 * whileStmt      -> "while" "(" expression ")" statement ;
 * forStmt        -> "for" "(" ( varDecl | exprStmt | ";" )
 *                    expression? ";"
 *                    expression? ";" statement ;
 * blockStmt      -> "{" declaration* "}" ;
 *
 * expression     -> assignment
 * assignment     -> IDENTIFIER "=" assignment
 *                 | logic_or ;
 * logic_or       -> logic_and ("or" logic_and)* ;
 * logic_and       -> equality ("and" equality)* ;
 * equality       -> comparison ( ( "!=" | "==" ) comparison )* ;
 * comparison     -> term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
 * term           -> factor ( ( "-" | "+" ) factor )* ;
 * factor         -> unary ( ( "/" | "*" ) unary )* ;
 * unary          -> ( "!" | "-" ) unary | call ;
 * call           -> primary ( "(" arguments? ")" )* ;
 * arguments      -> expression ( ","  expression )* ;
 * primary        -> NUMBER | STRING | "true" | "false" | "nil"
 *                 | "(" expression ") | IDENTIFIER ;
 */

pub struct Parser<'a> {
    lexer: Peekable<LexerIterator<'a>>,
    optional_semi_expressions: bool,
}

#[allow(clippy::result_large_err)]
impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>, optional_semi_expressions: bool) -> Self {
        Self {
            lexer: lexer.iter().peekable(),
            optional_semi_expressions,
        }
    }

    pub fn parse_program(&mut self) -> Result<Program, ParserOrTokenError> {
        let mut program = Program::new();

        while let Some(result) = self.lexer.next() {
            let token = result?;
            let statement = self.parse_declaration(token)?;

            program.statements.push(statement);
        }

        Ok(program)
    }

    fn parse_declaration(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        match &token.kind {
            TokenType::Var => self.parse_variable_statement(token),
            _ => self.parse_statement(token),
        }
    }

    fn parse_variable_statement(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        let identifier = self.advance_expecting(&token, TokenType::Identifier, |next| {
            ParserErrorType::IdentifierExpected {
                found: next.clone(),
            }
        })?;

        let next = self.advance(&identifier)?;

        match &next.kind {
            TokenType::Semicolon => Ok(Statement::var_declaration(token, identifier, None)),
            TokenType::Equal => {
                let next = self.advance(&identifier)?;
                let expression = self.parse_expression(next)?;

                self.expect_semi(&expression.token)?;

                Ok(Statement::var_declaration(
                    token,
                    identifier,
                    Some(expression),
                ))
            }
            _ => Err(ParserOrTokenError::Parser(ParserError::new(
                ParserErrorType::UnexpectedToken {
                    token: next.lexeme.clone(),
                },
                next,
            ))),
        }
    }

    fn parse_statement(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        match &token.kind {
            TokenType::Print => self.parse_print_statement(token),
            TokenType::LeftBrace => self.parse_block_statement(token),
            TokenType::If => self.parse_if_statement(token),
            TokenType::While => self.parse_while_statement(token),
            TokenType::For => self.parse_for_statement(token),
            _ => self.parse_expression_statement(token),
        }
    }

    fn parse_print_statement(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        let next = self.advance(&token)?;
        let expression = self.parse_expression(next.clone())?;

        self.expect_semi(&expression.token)?;
        Ok(Statement::new(
            token,
            StatementType::Print { expr: expression },
        ))
    }

    fn parse_block_statement(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        let mut last_token = None;
        let mut stmts = Vec::new();

        while let Some(next) = self.lexer.next() {
            let next = next?;
            last_token = Some(next.clone());
            if next.kind == TokenType::RightBrace {
                break;
            }
            let stmt = self.parse_declaration(next.clone())?;
            stmts.push(stmt);
        }

        if last_token.map_or(true, |tok| tok.kind != TokenType::RightBrace) {
            return Err(ParserOrTokenError::Parser(ParserError::new(
                ParserErrorType::BlockNotClosed,
                token,
            )));
        }

        Ok(Statement::new(token, StatementType::Block { stmts }))
    }

    fn parse_if_statement(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        let left_paren = self.advance_expecting_dft(&token, TokenType::LeftParen)?;
        let next = self.advance(&left_paren)?;
        let condition = self.parse_expression(next)?;
        self.advance_expecting_dft(&condition.token, TokenType::RightParen)?;

        let next = self.advance(&left_paren)?;
        let then = self.parse_statement(next)?;

        let else_block = if let Some(Ok(next)) = self.lexer.peek() {
            if next.kind == TokenType::Else {
                // consume the else
                let else_tok = self.lexer.next().unwrap().unwrap();

                let next = self.advance(&else_tok)?;
                let block = self.parse_statement(next)?;
                Some(Box::new(block))
            } else {
                None
            }
        } else {
            None
        };

        Ok(Statement::new(
            token,
            StatementType::If {
                condition,
                then: Box::new(then),
                else_block,
            },
        ))
    }

    fn parse_while_statement(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        let open_paren = self.advance_expecting_dft(&token, TokenType::LeftParen)?;
        let next = self.advance(&open_paren)?;
        let condition = self.parse_expression(next)?;
        let close_paren = self.advance_expecting_dft(&condition.token, TokenType::RightParen)?;

        let next = self.advance(&close_paren)?;
        let body = self.parse_statement(next)?;

        Ok(Statement::new(
            token,
            StatementType::While {
                condition,
                body: Box::new(body),
            },
        ))
    }

    // --- Desugar For Loop ---
    // A for loop `for (init; cond; incr) body` is syntactic sugar for:
    // {
    //   init;
    //   while (cond) {
    //     body;
    //     incr;
    //   }
    // }
    fn parse_for_statement(&mut self, token: Token) -> Result<Statement, ParserOrTokenError> {
        let mut stmts = Vec::new();
        let open_paren = self.advance_expecting_dft(&token, TokenType::LeftParen)?;

        // --- Parse Initializer ---
        // The initializer can be a variable declaration, an expression statement, or empty.
        let next = self.advance(&open_paren)?;
        let initializer = match next.kind {
            TokenType::Semicolon => None,
            TokenType::Var => {
                let var_decl = self.parse_variable_statement(next)?;
                Some(var_decl)
            }
            _ => {
                // Must be an expression statement or an error
                let expr_stmt = self.parse_expression_statement(next)?;
                Some(expr_stmt)
            }
        };
        stmts.extend(initializer);

        // --- Parse Condition ---
        // The condition is an optional expression followed by a semicolon.
        let next = self.advance(&open_paren)?;
        let (condition, condition_semi) = if next.kind == TokenType::Semicolon {
            (None, next)
        } else {
            // Must be an expression or an error
            let expr = self.parse_expression(next)?;
            let semi = self.expect_semi(&expr.token)?;
            (Some(expr), semi)
        };

        // --- Parse Increment ---
        // The increment is an optional expression followed by the closing parenthesis.
        let next = self.advance(&condition_semi)?;
        let (increment, rparen) = if next.kind == TokenType::RightParen {
            (None, next)
        } else {
            let expr = self.parse_expression(next)?;
            let rparen = self.advance_expecting_dft(&expr.token, TokenType::RightParen)?;
            (Some(Statement::expression(expr)), rparen)
        };

        // --- Parse Body ---
        let next = self.advance(&rparen)?;
        let mut body = self.parse_statement(next)?;

        // 1. Add the increment to the end of the body block.
        if let Some(inc_stmt) = increment {
            body = Statement::new(
                body.token.clone(),
                StatementType::Block {
                    stmts: vec![body, inc_stmt],
                },
            )
        }

        // 2. Create the while loop (condition defaults to true if omitted).
        let condition_expr = condition.unwrap_or_else(|| {
            Expression::literal(
                Token::genereted(TokenType::True, "true"),
                LiteralExpression::True,
            )
        });

        let while_stmt = Statement::new(
            token.clone(),
            StatementType::While {
                condition: condition_expr,
                body: Box::new(body),
            },
        );
        stmts.push(while_stmt);

        // 3. Wrap the while loop in a block.
        Ok(Statement::new(token, StatementType::Block { stmts }))
    }

    fn parse_expression_statement(
        &mut self,
        token: Token,
    ) -> Result<Statement, ParserOrTokenError> {
        let expression = self.parse_expression(token.clone())?;

        if let Some(Ok(next)) = self.lexer.peek() {
            if next.kind == TokenType::Semicolon {
                self.lexer.next();
            } else if !self.optional_semi_expressions {
                return Err(ParserOrTokenError::Parser(ParserError::new(
                    ParserErrorType::MissingSemicolen,
                    expression.token,
                )));
            }
        }
        Ok(Statement::expression(expression))
    }

    fn parse_expression(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        self.parse_assignment(token)
    }

    fn parse_assignment(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        let left = self.parse_logic_or(token)?;

        if let Some(Ok(next)) = self.lexer.peek() {
            if next.kind == TokenType::Equal {
                let equals = next.clone();
                self.lexer.next();
                let next = self.advance(&equals)?;

                let rigth = self.parse_assignment(next)?;

                return match left.kind {
                    ExpressionType::Identifier(IdentifierStruct { name }) => Ok(Expression::new(
                        equals,
                        ExpressionType::Assignment {
                            kind: AssignmentKind::Variable { name },
                            value: Box::new(rigth),
                        },
                    )),
                    _ => Err(ParserOrTokenError::Parser(ParserError::new(
                        ParserErrorType::InvalidAssignmentTarget,
                        equals,
                    ))),
                };
            }
        }

        Ok(left)
    }

    fn parse_logic_or(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        self.parse_binary_operation(token, Self::parse_logic_and, &[TokenType::Or])
    }

    fn parse_logic_and(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        self.parse_binary_operation(token, Self::parse_equality, &[TokenType::And])
    }

    fn parse_equality(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        self.parse_binary_operation(
            token,
            Self::parse_comparison,
            &[TokenType::EqualEqual, TokenType::BangEqual],
        )
    }

    fn parse_comparison(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
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

    fn parse_term(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        self.parse_binary_operation(
            token,
            Self::parse_factor,
            &[TokenType::Plus, TokenType::Minus],
        )
    }

    fn parse_factor(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        self.parse_binary_operation(
            token,
            Self::parse_unary,
            &[TokenType::Star, TokenType::Slash],
        )
    }

    fn parse_unary(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
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
            self.parse_call(token)
        }
    }

    fn parse_call(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        let mut primary = self.parse_primary(token)?;

        while let Some(Ok(next)) = self.lexer.peek().cloned() {
            if next.kind == TokenType::LeftParen {
                self.lexer.next().unwrap().unwrap();
                let arguments = self.parse_arguments(&next)?;

                primary = Expression::new(
                    next,
                    ExpressionType::Call {
                        calee: Box::new(primary),
                        arguments,
                    },
                );
            } else {
                break;
            }
        }

        Ok(primary)
    }

    fn parse_arguments(
        &mut self,
        prev_token: &Token,
    ) -> Result<Vec<Expression>, ParserOrTokenError> {
        let mut args = Vec::new();
        let mut prev_token = prev_token.clone();

        loop {
            let next = self.advance(&prev_token)?;
            if next.kind == TokenType::RightParen {
                break;
            }
            if args.len() >= 255 {
                return Err(ParserOrTokenError::Parser(ParserError::new(
                    ParserErrorType::TooManyArguments,
                    next,
                )));
            }

            let arg = self.parse_expression(next.clone())?;
            args.push(arg);

            let next = self.advance(&prev_token)?;
            match &next.kind {
                TokenType::RightParen => break,
                TokenType::Comma => (),
                _ => {
                    return Err(ParserOrTokenError::Parser(ParserError::new(
                        ParserErrorType::UnmatchedParenthesis,
                        next,
                    )))
                }
            }

            prev_token = next;
        }

        Ok(args)
    }

    fn parse_primary(&mut self, token: Token) -> Result<Expression, ParserOrTokenError> {
        match &token.kind {
            TokenType::LeftParen => {
                let next_token = self.advance(&token)?;
                let inner = self.parse_expression(next_token)?;

                self.advance_expecting(&inner.token, TokenType::RightParen, |_| {
                    ParserErrorType::UnmatchedParenthesis
                })?;
                Ok(Expression::new(
                    token,
                    ExpressionType::Grouping {
                        expr: Box::new(inner),
                    },
                ))
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
            TokenType::Identifier => {
                let name = token.lexeme.clone();
                Ok(Expression::new(token, ExpressionType::identifier(name)))
            }
            _ => Err(ParserOrTokenError::Parser(ParserError::new(
                ParserErrorType::UnexpectedToken {
                    token: token.lexeme.clone(),
                },
                token,
            ))),
        }
    }

    // Helper functions

    fn parse_binary_operation<F>(
        &mut self,
        token: Token,
        parse_lower: F,
        operators: &[TokenType],
    ) -> Result<Expression, ParserOrTokenError>
    where
        F: Fn(&mut Self, Token) -> Result<Expression, ParserOrTokenError>,
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
                        right: Box::new(right),
                    },
                );
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn advance(&mut self, prev_token: &Token) -> Result<Token, ParserOrTokenError> {
        match self.lexer.next() {
            Some(result) => result.map_err(ParserOrTokenError::Token),
            None => Err(ParserOrTokenError::Parser(ParserError::new(
                ParserErrorType::UnexpectedEof,
                prev_token.clone(),
            ))),
        }
    }

    fn advance_expecting<F>(
        &mut self,
        prev_token: &Token,
        expected: TokenType,
        error: F,
    ) -> Result<Token, ParserOrTokenError>
    where
        F: FnOnce(&Token) -> ParserErrorType,
    {
        let next = self.advance(prev_token)?;
        if next.kind == expected {
            Ok(next)
        } else {
            Err(ParserOrTokenError::Parser(ParserError::new(
                error(&next),
                next.clone(),
            )))
        }
    }

    fn advance_expecting_dft(
        &mut self,
        prev_token: &Token,
        expected: TokenType,
    ) -> Result<Token, ParserOrTokenError> {
        self.advance_expecting(prev_token, expected.clone(), |tok| {
            ParserErrorType::ExpectedNotFound {
                expected,
                found: tok.kind.clone(),
            }
        })
    }

    fn expect_semi(&mut self, prev_token: &Token) -> Result<Token, ParserOrTokenError> {
        self.advance_expecting(prev_token, TokenType::Semicolon, |_| {
            ParserErrorType::MissingSemicolen
        })
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ParserOrTokenError {
    #[error("{0}")]
    Parser(#[from] ParserError),

    #[error("{0}")]
    Token(#[from] TokenError),
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParserError {
    pub error: ParserErrorType,
    pub token: Token,
}

impl ParserError {
    pub fn new(error: ParserErrorType, token: Token) -> Self {
        Self { error, token }
    }
}

impl Display for ParserError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[line {}] Error at '{}': {}",
            self.token.line, self.token.lexeme, self.error
        )
    }
}

impl Error for ParserError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.error)
    }
}

#[derive(Debug, thiserror::Error, PartialEq, Clone)]
pub enum ParserErrorType {
    #[error("Unexpected token '{token}'")]
    UnexpectedToken { token: String },

    #[error("Expected '{expected}', but found '{found}'")]
    ExpectedNotFound {
        expected: TokenType,
        found: TokenType,
    },

    #[error("Expected closing ')'")]
    UnmatchedParenthesis,

    #[error("Missing ';'")]
    MissingSemicolen,

    #[error("Identifier expected. Foud: {:?}", found)]
    IdentifierExpected { found: Token },

    #[error("Invalid assignment target.")]
    InvalidAssignmentTarget,

    #[error("Block not closed.")]
    BlockNotClosed,

    #[error("Can't have more than 255 arguments.")]
    TooManyArguments,

    #[error("Unexpected end of file")]
    UnexpectedEof,
}

#[cfg(test)]
mod tests {

    fn parse_program(input: &str) -> String {
        let program = super::parse_program(input, true).expect("Program did not parse correctly");

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
            assert_eq!(parse_program(input), expected, "Input: {}", input);
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
            assert_eq!(parse_program(input), expected, "Input: {}", input);
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
            assert_eq!(parse_program(input), expected, "Input: {}", input);
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
            assert_eq!(parse_program(input), expected, "Input: {}", input);
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
            assert_eq!(parse_program(input), expected, "Input: {}", input);
        }
    }

    #[test]
    fn parse_identifier_and_declaration() {
        let tests = vec![
            ("var name = \"John\";", "var name = John;"),
            ("var Uninitialized;", "var Uninitialized;"),
            ("variable + 23", "(+ variable 23.0)"),
        ];

        for (input, expected) in tests {
            assert_eq!(parse_program(input), expected, "Input: {}", input);
        }
    }

    #[test]
    fn parse_block() {
        let tests = vec![
            ("{}", "{\n\n}"),
            ("{ 1 + 2; }", "{\n(+ 1.0 2.0)\n}"),
            ("{ 2 * 4; 43 /32; }", "{\n(* 2.0 4.0)\n(/ 43.0 32.0)\n}"),
        ];

        for (input, expected) in tests {
            assert_eq!(parse_program(input), expected, "Input: {}", input);
        }
    }
}

use std::fmt::{Debug, Display, Formatter};

use crate::token::Token;

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Program {
    pub fn new() -> Self {
        Self {
            statements: Vec::new(),
        }
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct Statement {
    pub token: Token,
    pub kind: StatementType,
}

impl Statement {
    pub fn new(token: Token, kind: StatementType) -> Self {
        Self { token, kind }
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            StatementType::Expression { expr } => write!(f, "{}", expr),
        }
    }
}

#[derive(Debug)]
pub enum StatementType {
    Expression { expr: Expression },
}

#[derive(Debug)]
pub struct Expression {
    pub token: Token,
    pub kind: ExpressionType,
}

impl Expression {
    pub fn new(token: Token, kind: ExpressionType) -> Self {
        Self { token, kind }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ExpressionType::Literal { literal } => write!(f, "{}", literal),
            ExpressionType::Unary { operator, expr } => write!(f, "({} {})", operator, expr),
            ExpressionType::Binary {
                left,
                operator,
                rigth,
            } => write!(f, "({} {} {})", operator, left, rigth),
            ExpressionType::Grouping { expr } => write!(f, "(group {})", expr),
        }
    }
}

#[derive(Debug)]
pub enum ExpressionType {
    Literal {
        literal: LiteralExpression,
    },
    Unary {
        operator: UnaryOperator,
        expr: Box<Expression>,
    },
    Binary {
        left: Box<Expression>,
        operator: BinaryOperator,
        rigth: Box<Expression>,
    },
    Grouping {
        expr: Box<Expression>,
    },
}

#[derive(Debug)]
pub enum LiteralExpression {
    Number { literal: f64 },
    String { literal: String },
    True,
    False,
    Nil,
}

impl Display for LiteralExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralExpression::Number { literal } => write!(f, "{:?}", literal),
            LiteralExpression::String { literal } => write!(f, "{}", literal),
            LiteralExpression::True => write!(f, "true"),
            LiteralExpression::False => write!(f, "false"),
            LiteralExpression::Nil => write!(f, "nil"),
        }
    }
}

#[derive(Debug)]
pub enum UnaryOperator {
    Negative,
    Negation,
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Negative => write!(f, "-"),
            UnaryOperator::Negation => write!(f, "!"),
        }
    }
}

#[derive(Debug)]
pub enum BinaryOperator {
    Equals,
    NotEquals,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Plus,
    Minus,
    Times,
    Divide,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Equals => write!(f, "="),
            BinaryOperator::NotEquals => write!(f, "!="),
            BinaryOperator::Less => write!(f, "<"),
            BinaryOperator::LessEqual => write!(f, "<="),
            BinaryOperator::Greater => write!(f, ">"),
            BinaryOperator::GreaterEqual => write!(f, ">="),
            BinaryOperator::Plus => write!(f, "+"),
            BinaryOperator::Minus => write!(f, "-"),
            BinaryOperator::Times => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/"),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::TokenType;

    fn fake_token() -> Token {
        Token::new(TokenType::Semicolon, "", 0, 0)
    }

    fn fake_expression(kind: ExpressionType) -> Expression {
        Expression::new(fake_token(), kind)
    }

    #[test]
    fn test_literal_expression_number() {
        let expr = fake_expression(ExpressionType::Literal {
            literal: LiteralExpression::Number { literal: 45.67 },
        });
        assert_eq!(expr.to_string(), "45.67");
    }

    #[test]
    fn test_literal_expression_string() {
        let expr = fake_expression(ExpressionType::Literal {
            literal: LiteralExpression::String {
                literal: "hello".to_string(),
            },
        });
        assert_eq!(expr.to_string(), "hello");
    }

    #[test]
    fn test_unary_expression_negative() {
        let expr = fake_expression(ExpressionType::Unary {
            operator: UnaryOperator::Negative,
            expr: Box::new(fake_expression(ExpressionType::Literal {
                literal: LiteralExpression::Number { literal: 123.0 },
            })),
        });
        assert_eq!(expr.to_string(), "(- 123.0)");
    }

    #[test]
    fn test_binary_expression() {
        let expr = fake_expression(ExpressionType::Binary {
            left: Box::new(fake_expression(ExpressionType::Unary {
                operator: UnaryOperator::Negative,
                expr: Box::new(fake_expression(ExpressionType::Literal {
                    literal: LiteralExpression::Number { literal: 123.0 },
                })),
            })),
            operator: BinaryOperator::Times,
            rigth: Box::new(fake_expression(ExpressionType::Grouping {
                expr: Box::new(fake_expression(ExpressionType::Literal {
                    literal: LiteralExpression::Number { literal: 45.67 },
                })),
            })),
        });
        assert_eq!(expr.to_string(), "(* (- 123.0) (group 45.67))");
    }

    #[test]
    fn test_grouping_expression() {
        let expr = fake_expression(ExpressionType::Grouping {
            expr: Box::new(fake_expression(ExpressionType::Literal {
                literal: LiteralExpression::Number { literal: 45.67 },
            })),
        });
        assert_eq!(expr.to_string(), "(group 45.67)");
    }

    #[test]
    fn test_statement_expression() {
        let stmt = Statement::new(
            fake_token(),
            StatementType::Expression {
                expr: fake_expression(ExpressionType::Literal {
                    literal: LiteralExpression::True,
                }),
            },
        );
        assert_eq!(stmt.to_string(), "true");
    }
}
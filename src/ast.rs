use std::fmt::{Debug, Display, Formatter};

use crate::token::Token;

#[derive(Debug, Clone)]
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

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let as_str = self
            .statements
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        write!(f, "{}", as_str)
    }
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub token: Token,
    pub kind: StatementType,
}

impl Statement {
    pub fn new(token: Token, kind: StatementType) -> Self {
        Self { token, kind }
    }

    pub fn expression(expression: Expression) -> Self {
        Self::new(
            expression.token.clone(),
            StatementType::Expression { expr: expression },
        )
    }

    pub fn var_declaration(var_token: Token, identifier: Token, value: Option<Expression>) -> Self {
        Self::new(
            var_token,
            StatementType::Declaration {
                stmt: DeclaraionStatement::VarDeclaration {
                    identifier: IdentifierStruct {
                        name: identifier.lexeme,
                    },
                    value,
                },
            },
        )
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            StatementType::Expression { expr } => write!(f, "{};", expr),
            StatementType::Print { expr } => write!(f, "print {};", expr),
            StatementType::Declaration { stmt } => match stmt {
                DeclaraionStatement::VarDeclaration { identifier, value } => {
                    if let Some(value) = value {
                        write!(f, "var {} = {};", identifier.name, value)
                    } else {
                        write!(f, "var {};", identifier.name)
                    }
                }
                DeclaraionStatement::FunctionDeclaration(FunctionDeclarationStruct {
                    identifier,
                    params,
                    body,
                }) => {
                    let params = params
                        .iter()
                        .map(|it| it.name.clone())
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "fun {}({}) {}", identifier.name, params, body)
                }
            },
            StatementType::Block { stmts } => {
                let stmts = stmts
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join("\n");
                write!(f, "{{\n{}\n}}", stmts)
            }
            StatementType::If {
                condition,
                then,
                else_block,
            } => {
                write!(f, "if ({}) {{\n{}}}", condition, then)?;
                if let Some(else_block) = else_block {
                    write!(f, "\nelse {{\n{}}}", else_block)?;
                }

                Ok(())
            }
            StatementType::While { condition, body } => {
                write!(f, "while ({}) {{\n{}}}", condition, body)
            }
            StatementType::Return { expr: value } => write!(
                f,
                "return {};",
                if let Some(value) = value {
                    value.to_string()
                } else {
                    "nil".to_string()
                }
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub enum StatementType {
    Expression {
        expr: Expression,
    },
    Print {
        expr: Expression,
    },
    Declaration {
        stmt: DeclaraionStatement,
    },
    Block {
        stmts: Vec<Statement>,
    },
    While {
        condition: Expression,
        body: Box<Statement>,
    },
    If {
        condition: Expression,
        then: Box<Statement>,
        else_block: Option<Box<Statement>>,
    },
    Return {
        expr: Option<Expression>,
    },
}

#[derive(Debug, Clone)]
pub struct Expression {
    pub token: Token,
    pub kind: ExpressionType,
}

impl Expression {
    pub fn new(token: Token, kind: ExpressionType) -> Self {
        Self { token, kind }
    }

    pub fn literal(token: Token, literal: LiteralExpression) -> Self {
        Self::new(token, ExpressionType::Literal { literal })
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
                right: rigth,
            } => write!(f, "({} {} {})", operator, left, rigth),
            ExpressionType::Grouping { expr } => write!(f, "(group {})", expr),
            ExpressionType::Identifier(IdentifierStruct { name }) => write!(f, "{}", name),
            ExpressionType::Assignment { kind, value } => match kind {
                AssignmentKind::Variable { name } => write!(f, "{} = {}", name, value),
            },
            ExpressionType::Call { calee, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|it| it.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({}({}))", calee, arguments)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct IdentifierStruct {
    pub name: String,
}

#[derive(Debug, Clone)]
pub enum AssignmentKind {
    Variable { name: String },
}

#[derive(Debug, Clone)]
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
        right: Box<Expression>,
    },
    Grouping {
        expr: Box<Expression>,
    },
    Identifier(IdentifierStruct),
    Assignment {
        kind: AssignmentKind,
        value: Box<Expression>,
    },
    Call {
        calee: Box<Expression>,
        arguments: Vec<Expression>,
    },
}

impl ExpressionType {
    pub fn identifier(name: String) -> Self {
        Self::Identifier(IdentifierStruct { name })
    }
}

#[derive(Debug, Clone)]
pub enum LiteralExpression {
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

impl Display for LiteralExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralExpression::Number(literal) => write!(f, "{:?}", literal),
            LiteralExpression::String(literal) => write!(f, "{}", literal),
            LiteralExpression::True => write!(f, "true"),
            LiteralExpression::False => write!(f, "false"),
            LiteralExpression::Nil => write!(f, "nil"),
        }
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
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

    LogicOr,
    LogicAnd,
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Equals => write!(f, "=="),
            BinaryOperator::NotEquals => write!(f, "!="),
            BinaryOperator::Less => write!(f, "<"),
            BinaryOperator::LessEqual => write!(f, "<="),
            BinaryOperator::Greater => write!(f, ">"),
            BinaryOperator::GreaterEqual => write!(f, ">="),
            BinaryOperator::Plus => write!(f, "+"),
            BinaryOperator::Minus => write!(f, "-"),
            BinaryOperator::Times => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/"),
            BinaryOperator::LogicOr => write!(f, "or"),
            BinaryOperator::LogicAnd => write!(f, "and"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum DeclaraionStatement {
    VarDeclaration {
        identifier: IdentifierStruct,
        value: Option<Expression>,
    },
    FunctionDeclaration(FunctionDeclarationStruct),
}

#[derive(Debug, Clone)]
pub struct FunctionDeclarationStruct {
    pub identifier: IdentifierStruct,
    pub params: Vec<IdentifierStruct>,
    pub body: Box<Statement>,
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
            literal: LiteralExpression::Number(45.67),
        });
        assert_eq!(expr.to_string(), "45.67");
    }

    #[test]
    fn test_literal_expression_string() {
        let expr = fake_expression(ExpressionType::Literal {
            literal: LiteralExpression::String("hello".to_string()),
        });
        assert_eq!(expr.to_string(), "hello");
    }

    #[test]
    fn test_unary_expression_negative() {
        let expr = fake_expression(ExpressionType::Unary {
            operator: UnaryOperator::Negative,
            expr: Box::new(fake_expression(ExpressionType::Literal {
                literal: LiteralExpression::Number(123.0),
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
                    literal: LiteralExpression::Number(123.0),
                })),
            })),
            operator: BinaryOperator::Times,
            right: Box::new(fake_expression(ExpressionType::Grouping {
                expr: Box::new(fake_expression(ExpressionType::Literal {
                    literal: LiteralExpression::Number(45.67),
                })),
            })),
        });
        assert_eq!(expr.to_string(), "(* (- 123.0) (group 45.67))");
    }

    #[test]
    fn test_grouping_expression() {
        let expr = fake_expression(ExpressionType::Grouping {
            expr: Box::new(fake_expression(ExpressionType::Literal {
                literal: LiteralExpression::Number(45.67),
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
        assert_eq!(stmt.to_string(), "true;");
    }
}

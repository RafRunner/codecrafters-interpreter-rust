use crate::ast::{
    BinaryOperator, Expression, ExpressionType, LiteralExpression, Program, StatementType,
    UnaryOperator,
};
use anyhow::{anyhow, Result};

use super::object::Object;

pub fn evaluate(program: Program) -> Result<Object> {
    let mut output = Object::Nil;

    for stmt in program.statements {
        output = match stmt.kind {
            StatementType::Expression { expr } => execute_expression(expr)?,
        };
    }

    Ok(output)
}

fn execute_expression(expression: Expression) -> Result<Object> {
    match expression.kind {
        ExpressionType::Literal { literal } => match literal {
            LiteralExpression::Number { literal } => Ok(Object::Number(literal)),
            LiteralExpression::String { literal } => Ok(Object::String(literal)),
            LiteralExpression::True => Ok(Object::True),
            LiteralExpression::False => Ok(Object::False),
            LiteralExpression::Nil => Ok(Object::Nil),
        },
        ExpressionType::Unary { operator, expr } => {
            let inner = execute_expression(*expr)?;

            match operator {
                UnaryOperator::Negative => match inner {
                    Object::Number(n) => Ok(Object::Number(-n)),
                    _ => Err(anyhow!("Unary '-' can only be applied to numbers")),
                },
                UnaryOperator::Negation => match inner {
                    Object::True => Ok(Object::False),
                    Object::False => Ok(Object::True),
                    _ => Err(anyhow!("Unary '!' can only be applied to booleans")),
                },
            }
        }
        ExpressionType::Binary {
            left,
            operator,
            rigth,
        } => {
            let left_value = execute_expression(*left)?;
            let right_value = execute_expression(*rigth)?;

            match operator {
                BinaryOperator::Equals => Ok(Object::bool_as_obj(left_value == right_value)),
                BinaryOperator::NotEquals => Ok(Object::bool_as_obj(left_value != right_value)),
                BinaryOperator::Less => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => Ok(Object::bool_as_obj(l < r)),
                    _ => Err(anyhow!("Binary '<' can only be applied to numbers")),
                },
                BinaryOperator::LessEqual => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => Ok(Object::bool_as_obj(l <= r)),
                    _ => Err(anyhow!("Binary '<=' can only be applied to numbers")),
                },
                BinaryOperator::Greater => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => Ok(Object::bool_as_obj(l > r)),
                    _ => Err(anyhow!("Binary '>' can only be applied to numbers")),
                },
                BinaryOperator::GreaterEqual => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => Ok(Object::bool_as_obj(l >= r)),
                    _ => Err(anyhow!("Binary '>=' can only be applied to numbers")),
                },
                BinaryOperator::Plus => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => Ok(Object::Number(l + r)),
                    (Object::String(l), Object::String(r)) => Ok(Object::String(l + &r)),
                    _ => Err(anyhow!(
                        "Binary '+' can only be applied to numbers or concatenated with strings"
                    )),
                },
                BinaryOperator::Minus => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => Ok(Object::Number(l - r)),
                    _ => Err(anyhow!("Binary '-' can only be applied to numbers")),
                },
                BinaryOperator::Times => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => Ok(Object::Number(l * r)),
                    _ => Err(anyhow!("Binary '*' can only be applied to numbers")),
                },
                BinaryOperator::Divide => match (left_value, right_value) {
                    (Object::Number(l), Object::Number(r)) => {
                        if r != 0.0 {
                            Ok(Object::Number(l / r))
                        } else {
                            Err(anyhow!("Division by zero is not allowed"))
                        }
                    }
                    _ => Err(anyhow!("Binary '/' can only be applied to numbers")),
                },
            }
        }
        ExpressionType::Grouping { expr } => execute_expression(*expr),
    }
}

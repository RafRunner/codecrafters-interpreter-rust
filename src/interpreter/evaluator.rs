use std::collections::HashMap;

use crate::ast::{
    BinaryOperator, DeclaraionStatement, Expression, ExpressionType, IdentifierStruct, LiteralExpression, Program, StatementType, UnaryOperator
};
use anyhow::{anyhow, Result};

use super::object::Object;

pub struct Interpreter {
    // TODO just a temp env to pass the first stage
    env: HashMap<String, Object>
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            env: HashMap::new()
        }
    }

    pub fn evaluate(&mut self, program: Program) -> Result<Option<Object>> {
        let mut output = None;

        for stmt in program.statements {
            output = match stmt.kind {
                StatementType::Expression { expr } => Some(self.execute_expression(expr)?),
                StatementType::Print { expr } => {
                    let to_print = self.execute_expression(expr)?;

                    println!("{}", to_print);

                    None
                }
                StatementType::Declaration { stmt } => {
                    match stmt {
                        DeclaraionStatement::VarDeclaration { identifier, value } => {
                            let value = if let Some(expr) = value {
                                self.execute_expression(expr)?
                            } else {
                                Object::Nil
                            };

                            self.env.insert(identifier.name, value);

                            None
                        },
                    }
                },
            };
        }

        Ok(output)
    }

    pub fn execute_expression(&mut self, expression: Expression) -> Result<Object> {
        match expression.kind {
            ExpressionType::Literal { literal } => match literal {
                LiteralExpression::Number(literal) => Ok(Object::Number(literal)),
                LiteralExpression::String(literal) => Ok(Object::String(literal)),
                LiteralExpression::True => Ok(Object::True),
                LiteralExpression::False => Ok(Object::False),
                LiteralExpression::Nil => Ok(Object::Nil),
            },
            ExpressionType::Unary { operator, expr } => {
                let inner = self.execute_expression(*expr)?;

                match operator {
                    UnaryOperator::Negative => match inner {
                        Object::Number(n) => Ok(Object::Number(-n)),
                        _ => Err(anyhow!("Unary '-' can only be applied to numbers")),
                    },
                    UnaryOperator::Negation => Ok(Object::bool_as_obj(!inner.is_truthy())),
                }
            }
            ExpressionType::Binary {
                left,
                operator,
                rigth,
            } => {
                let left_value = self.execute_expression(*left)?;
                let right_value = self.execute_expression(*rigth)?;

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
            ExpressionType::Grouping { expr } => self.execute_expression(*expr),
            ExpressionType::Identifier(IdentifierStruct { name }) => {
                self.env.get(&name).cloned().ok_or(anyhow!("Undefined variable '{}'", name))
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse_program;

    use super::*;

    fn evaluate(program: Program) -> Result<Object> {
        Interpreter::new().evaluate(program).map(|res| res.unwrap())
    }

    #[test]
    fn test_evaluate_literals() {
        let tests = vec![
            ("nil", Object::Nil),
            ("true", Object::True),
            ("false", Object::False),
            ("23", Object::Number(23.0)),
            ("0.321", Object::Number(0.321)),
            ("\"olá, mundo!\"", Object::String("olá, mundo!".to_string())),
            ("\"\"", Object::String(String::new())),
        ];

        for (input, expected) in tests {
            let program = parse_program(input).unwrap();
            assert_eq!(evaluate(program).unwrap(), expected, "Input: {}", input);
        }
    }

    #[test]
    fn test_evaluate_unary_operations() {
        let tests = vec![
            ("-5", Object::Number(-5.0)),
            ("-3.14", Object::Number(-3.14)),
            ("!true", Object::False),
            ("!false", Object::True),
            ("!!true", Object::True),
            ("!nil", Object::True),
        ];

        for (input, expected) in tests {
            let program = parse_program(input).unwrap();
            assert_eq!(evaluate(program).unwrap(), expected, "Input: {}", input);
        }
    }

    #[test]
    fn test_evaluate_binary_operations() {
        let tests = vec![
            ("3 + 4", Object::Number(7.0)),
            ("10 - 2", Object::Number(8.0)),
            ("2 * 3", Object::Number(6.0)),
            ("8 / 2", Object::Number(4.0)),
            ("1 < 2", Object::True),
            ("2 > 1", Object::True),
            ("1 == 1", Object::True),
            ("1 != 2", Object::True),
            ("1 <= 1", Object::True),
            ("2 >= 2", Object::True),
            (
                "\"hello\" + \" world\"",
                Object::String("hello world".to_string()),
            ),
            ("3 + 2 * 4", Object::Number(11.0)), // Test operator precedence
            ("(3 + 2) * 4", Object::Number(20.0)), // Test grouping
        ];

        for (input, expected) in tests {
            let program = parse_program(input).unwrap();
            assert_eq!(evaluate(program).unwrap(), expected, "Input: {}", input);
        }
    }

    #[test]
    fn test_evaluate_complex_expressions() {
        let tests = vec![
            ("-(-3 + 2) * 4", Object::Number(4.0)),
            ("!(3 > 2)", Object::False),
            ("(5 - 3) * -(7 / 2) - 10", Object::Number(-17.0)),
            ("2 * 3 + 4 > 1 + 1", Object::True),
            ("42 + 1 > 34 == 10 + 10 /2 < 32.43", Object::True),
        ];

        for (input, expected) in tests {
            let program = parse_program(input).unwrap();
            assert_eq!(evaluate(program).unwrap(), expected, "Input: {}", input);
        }
    }

    #[test]
    fn test_evaluate_errors() {
        let tests = vec![
            (
                "\"hello\" - \"world\"",
                "Binary '-' can only be applied to numbers",
            ),
            ("5 / 0", "Division by zero is not allowed"),
            (
                "37 + \"foo\" + 47",
                "Binary '+' can only be applied to numbers or concatenated with strings",
            ),
            (
                "true >= false",
                "Binary '>=' can only be applied to numbers",
            ),
        ];

        for (input, expected_err) in tests {
            let program = parse_program(input).unwrap();
            let result = evaluate(program);
            assert!(result.is_err(), "Expression {} should be an error", input);
            assert_eq!(
                result.unwrap_err().to_string(),
                expected_err,
                "Input: {}",
                input
            );
        }
    }
}

use crate::ast::{
    AssignmentKind, BinaryOperator, DeclaraionStatement, Expression, ExpressionType,
    IdentifierStruct, LiteralExpression, Program, Statement, StatementType, UnaryOperator,
};
use anyhow::{anyhow, Result};

use super::{
    env::{Env, Symbol},
    object::Object,
};

#[derive(Debug, Default)]
pub struct Interpreter {
    // TODO just a temp env to pass the first stage
    env: Env,
}

impl Interpreter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn evaluate(&mut self, program: Program) -> Result<Option<Object>> {
        self.evaluate_statements(&program.statements)
    }

    fn evaluate_statements(&mut self, statements: &[Statement]) -> Result<Option<Object>> {
        let mut output = None;

        for stmt in statements {
            output = self.execute_statement(stmt)?;
        }

        Ok(output)
    }

    fn execute_statement(&mut self, stmt: &Statement) -> Result<Option<Object>> {
        match &stmt.kind {
            StatementType::Expression { expr } => self.execute_expression_statement(expr),
            StatementType::Print { expr } => self.execute_print_statement(expr).map(|_| None),
            StatementType::Declaration { stmt } => {
                self.execute_declaration_statement(stmt).map(|_| None)
            }
            StatementType::Block { stmts } => self.execute_block_statement(stmts),
            StatementType::If {
                condition,
                then,
                else_block,
            } => self
                .execute_if_statement(condition, then, else_block.as_deref())
                .map(|_| None),
            StatementType::While { condition, body } => {
                self.execute_while_statement(condition, body).map(|_| None)
            }
        }
    }

    fn execute_expression_statement(&mut self, expr: &Expression) -> Result<Option<Object>> {
        Ok(Some(self.execute_expression(expr)?))
    }

    fn execute_print_statement(&mut self, expr: &Expression) -> Result<()> {
        let to_print = self.execute_expression(expr)?;
        println!("{}", to_print);
        Ok(())
    }

    fn execute_declaration_statement(&mut self, stmt: &DeclaraionStatement) -> Result<()> {
        match stmt {
            DeclaraionStatement::VarDeclaration { identifier, value } => {
                let value = if let Some(expr) = value {
                    self.execute_expression(expr)?
                } else {
                    Object::Nil
                };
                self.env
                    .insert_symbol(identifier.name.clone(), Symbol::Variable(value));
            }
        };

        Ok(())
    }

    fn execute_block_statement(&mut self, stmts: &[Statement]) -> Result<Option<Object>> {
        self.env.enter_scope();
        let result = self.evaluate_statements(stmts);
        self.env.exit_scope();
        result
    }

    fn execute_if_statement(
        &mut self,
        condition: &Expression,
        then: &Statement,
        else_block: Option<&Statement>,
    ) -> Result<()> {
        if self.execute_expression(condition)?.is_truthy() {
            self.execute_statement(then)?;
        } else if let Some(else_block) = else_block {
            self.execute_statement(else_block)?;
        }

        Ok(())
    }

    fn execute_while_statement(&mut self, condition: &Expression, body: &Statement) -> Result<()> {
        while self.execute_expression(condition)?.is_truthy() {
            self.execute_statement(body)?;
        }

        Ok(())
    }

    fn execute_expression(&mut self, expression: &Expression) -> Result<Object> {
        match &expression.kind {
            ExpressionType::Literal { literal } => Ok(self.execute_literal_expression(literal)),
            ExpressionType::Unary { operator, expr } => {
                self.execute_unary_expression(operator, expr)
            }
            ExpressionType::Binary {
                left,
                operator,
                right,
            } => self.execute_binary_expression(left, operator, right),
            ExpressionType::Grouping { expr } => self.execute_expression(expr),
            ExpressionType::Identifier(IdentifierStruct { name }) => {
                self.execute_identifier_expression(name.clone())
            }
            ExpressionType::Assignment { kind, value } => {
                self.execute_assignment_expression(kind, value)
            }
        }
    }

    fn execute_literal_expression(&mut self, literal: &LiteralExpression) -> Object {
        match literal {
            LiteralExpression::Number(literal) => Object::Number(*literal),
            LiteralExpression::String(literal) => Object::String(literal.clone()),
            LiteralExpression::True => Object::True,
            LiteralExpression::False => Object::False,
            LiteralExpression::Nil => Object::Nil,
        }
    }

    fn execute_unary_expression(
        &mut self,
        operator: &UnaryOperator,
        expr: &Expression,
    ) -> Result<Object> {
        let inner = self.execute_expression(expr)?;

        match operator {
            UnaryOperator::Negative => match inner {
                Object::Number(n) => Ok(Object::Number(-n)),
                _ => Err(anyhow!("Unary '-' can only be applied to numbers")),
            },
            UnaryOperator::Negation => Ok(Object::bool_as_obj(!inner.is_truthy())),
        }
    }

    fn execute_binary_expression(
        &mut self,
        left: &Expression,
        operator: &BinaryOperator,
        right: &Expression,
    ) -> Result<Object> {
        let left_value = self.execute_expression(left)?;
        let right_value = match &operator {
            // Short circuit
            BinaryOperator::LogicOr => {
                if left_value.is_truthy() {
                    return Ok(Object::True);
                } else {
                    return self
                        .execute_expression(right)
                        .map(|right_value| right_value.as_bool_obj());
                }
            }
            BinaryOperator::LogicAnd => {
                if !left_value.is_truthy() {
                    return Ok(Object::False);
                } else {
                    return self
                        .execute_expression(right)
                        .map(|right_value| right_value.as_bool_obj());
                }
            }
            _ => self.execute_expression(right)?,
        };

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
            BinaryOperator::LogicOr | BinaryOperator::LogicAnd => {
                panic!("Interpreter bug: logic operations should have been delt with above")
            }
        }
    }

    fn execute_identifier_expression(&mut self, name: String) -> Result<Object> {
        match self.env.get_symbol(&name) {
            Some(Symbol::Variable(var)) => Ok(var.clone()),
            None => Err(anyhow!("Undefined variable '{}'", name)),
        }
    }

    fn execute_assignment_expression(
        &mut self,
        kind: &AssignmentKind,
        value: &Expression,
    ) -> Result<Object> {
        match kind {
            AssignmentKind::Variable { name } => {
                let value = self.execute_expression(value)?;
                if let Some(symbol) = self.env.get_symbol(name) {
                    *symbol = Symbol::Variable(value.clone());
                    Ok(value)
                } else {
                    Err(anyhow!("Undefined variable '{}'", name))
                }
            }
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
            let program = parse_program(input, true).unwrap();
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
            let program = parse_program(input, true).unwrap();
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
            let program = parse_program(input, true).unwrap();
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
            let program = parse_program(input, true).unwrap();
            assert_eq!(evaluate(program).unwrap(), expected, "Input: {}", input);
        }
    }

    #[test]
    fn test_evaluate_if_expressions() {
        let source = "\
        var number1 = 10 + 5;
        var number2 = 3;
        var result;

        if (number1 > number2) {
            result = true;
        } else {
            result = false; 
        }
 
        result
        ";

        let program = parse_program(source, true).unwrap();
        assert_eq!(evaluate(program).unwrap(), Object::True);

        let source = "\
        var number1 = 43;
        var number2 = 21;
        var result = false;

        if (number2 + number1 > 100) {
            result = true;
        }
 
        result
        ";

        let program = parse_program(source, true).unwrap();
        assert_eq!(evaluate(program).unwrap(), Object::False);

        let source = "\
        var result;

        if (2 + 2 * 6 == 24)
            result = \"wrong\";
        else
            result = \"right\";
 
        result
        ";

        let program = parse_program(source, true).unwrap();
        assert_eq!(
            evaluate(program).unwrap(),
            Object::String(String::from("right"))
        );
    }

    #[test]
    fn test_while_statement() {
        let source = "\
        var i = 1;
        var sum = 0;

        while (i <= 10) {
            sum = sum + i;
            i = i + 1;
        }

        sum
        ";

        let program = parse_program(source, true).unwrap();
        assert_eq!(evaluate(program).unwrap(), Object::Number(55.0));
    }

    #[test]
    fn test_for_statement() {
        let source = "\
        var a = 0;
        var temp;

        for (var b = 1; a < 10000; b = temp + b) {
          temp = a;
          a = b;
        }

        a
        ";

        let program = parse_program(source, true).unwrap();
        assert_eq!(evaluate(program).unwrap(), Object::Number(10946.0));
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
            let program = parse_program(input, true).unwrap();
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

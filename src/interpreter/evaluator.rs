use std::{
    cell::RefCell,
    io::Write,
    rc::Rc,
    time::{SystemTime, UNIX_EPOCH},
};

use crate::ast::{
    AssignmentKind, BinaryOperator, DeclaraionStatement, Expression, ExpressionType,
    FunctionDeclarationStruct, IdentifierStruct, LiteralExpression, Program, Statement,
    StatementType, UnaryOperator,
};
use anyhow::{anyhow, Ok, Result};

use super::{env::Env, object::Object};

pub struct Interpreter {
    pub env: Rc<RefCell<Env>>,
    output: Rc<RefCell<dyn Write>>,
}

impl Interpreter {
    pub fn new(output: Rc<RefCell<dyn Write>>) -> Self {
        let mut env = Env::new();
        env.define(
            "clock",
            Object::new_native_fn("clock", 0, |_, _| {
                let timestamp = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
                Ok(Object::Number(timestamp as f64))
            }),
        );
        env.define(
            "str",
            Object::new_native_fn("str", 1, |_, args| Ok(Object::String(args[0].to_string()))),
        );

        Self {
            env: Rc::new(RefCell::new(env)),
            output,
        }
    }

    pub fn evaluate(&mut self, program: Program) -> Result<()> {
        self.evaluate_statements(&program.statements)?;
        Ok(())
    }

    fn evaluate_statements(&mut self, statements: &[Statement]) -> Result<Object> {
        let mut output = Object::Unit;

        for stmt in statements {
            let result = self.execute_statement(stmt)?;

            // If we encounter a return statement, propagate it upward
            if matches!(result, Object::Return(_)) {
                output = result;
                break;
            }
        }

        Ok(output)
    }

    pub fn execute_statement(&mut self, stmt: &Statement) -> Result<Object> {
        match &stmt.kind {
            StatementType::Expression { expr } => self
                .execute_expression_statement(expr)
                .map(|_| Object::Unit),
            StatementType::Print { expr } => {
                self.execute_print_statement(expr).map(|_| Object::Unit)
            }
            StatementType::Declaration { stmt } => self
                .execute_declaration_statement(stmt)
                .map(|_| Object::Unit),
            StatementType::Block { stmts } => self.execute_block_statement(stmts),
            StatementType::If {
                condition,
                then,
                else_block,
            } => self.execute_if_statement(condition, then, else_block.as_deref()),
            StatementType::While { condition, body } => {
                self.execute_while_statement(condition, body)
            }
            StatementType::Return { expr } => self.execute_return_statement(expr.as_ref()),
        }
    }

    fn execute_expression_statement(
        &mut self,
        expr: &Expression,
    ) -> std::result::Result<(), anyhow::Error> {
        self.execute_expression(expr)?;
        Ok(())
    }

    fn execute_print_statement(&mut self, expr: &Expression) -> Result<()> {
        let to_print = self.execute_expression(expr)?;
        writeln!(self.output.borrow_mut(), "{}", to_print)?;
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
                self.env.borrow_mut().define(&identifier.name, value);
            }
            DeclaraionStatement::FunctionDeclaration(FunctionDeclarationStruct {
                identifier,
                params,
                body,
            }) => {
                // Create a new user function by passing the parameters and body directly
                let user_fn = Object::new_user_fn(
                    &identifier.name,
                    params.clone(),
                    body.clone(),
                    self.env.borrow().clone(),
                );

                self.env.borrow_mut().define(&identifier.name, user_fn);
            }
        }

        Ok(())
    }

    fn execute_block_statement(&mut self, stmts: &[Statement]) -> Result<Object> {
        let previous_env = Rc::clone(&self.env);
        self.env = Env::new_from_parent(&previous_env);
        let result = self.evaluate_statements(stmts);
        self.env = previous_env;
        result
    }

    fn execute_if_statement(
        &mut self,
        condition: &Expression,
        then: &Statement,
        else_block: Option<&Statement>,
    ) -> Result<Object> {
        if self.execute_expression(condition)?.is_truthy() {
            self.execute_statement(then)
        } else if let Some(else_block) = else_block {
            self.execute_statement(else_block)
        } else {
            Ok(Object::Unit)
        }
    }

    fn execute_while_statement(
        &mut self,
        condition: &Expression,
        body: &Statement,
    ) -> Result<Object> {
        let mut return_value = Object::Unit;

        while self.execute_expression(condition)?.is_truthy() {
            let result = self.execute_statement(body)?;

            // Break the loop if we encounter a return statement
            if matches!(result, Object::Return(_)) {
                return_value = result;
                break;
            }
        }

        Ok(return_value)
    }

    fn execute_return_statement(&mut self, expr: Option<&Expression>) -> Result<Object> {
        let value = match expr {
            Some(e) => self.execute_expression(e)?,
            None => Object::Nil,
        };
        Ok(Object::Return(Box::new(value)))
    }

    pub fn execute_expression(&mut self, expression: &Expression) -> Result<Object> {
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
            ExpressionType::Call { calee, arguments } => {
                self.execute_call_expression(calee, arguments)
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
            UnaryOperator::Negation => Ok(Object::new_bool(!inner.is_truthy())),
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
                return if left_value.is_truthy() {
                    Ok(left_value)
                } else {
                    self.execute_expression(right)
                };
            }
            BinaryOperator::LogicAnd => {
                return if !left_value.is_truthy() {
                    Ok(left_value)
                } else {
                    self.execute_expression(right)
                };
            }
            _ => self.execute_expression(right)?,
        };

        match operator {
            BinaryOperator::Equals => Ok(Object::new_bool(left_value == right_value)),
            BinaryOperator::NotEquals => Ok(Object::new_bool(left_value != right_value)),
            BinaryOperator::Less => match (left_value, right_value) {
                (Object::Number(l), Object::Number(r)) => Ok(Object::new_bool(l < r)),
                _ => Err(anyhow!("Binary '<' can only be applied to numbers")),
            },
            BinaryOperator::LessEqual => match (left_value, right_value) {
                (Object::Number(l), Object::Number(r)) => Ok(Object::new_bool(l <= r)),
                _ => Err(anyhow!("Binary '<=' can only be applied to numbers")),
            },
            BinaryOperator::Greater => match (left_value, right_value) {
                (Object::Number(l), Object::Number(r)) => Ok(Object::new_bool(l > r)),
                _ => Err(anyhow!("Binary '>' can only be applied to numbers")),
            },
            BinaryOperator::GreaterEqual => match (left_value, right_value) {
                (Object::Number(l), Object::Number(r)) => Ok(Object::new_bool(l >= r)),
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
        match self.env.borrow().get_symbol(&name) {
            Some(var) => Ok(var),
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
                self.env.borrow_mut().assign(name, value.clone())?;
                Ok(value)
            }
        }
    }

    fn execute_call_expression(
        &mut self,
        callee: &Expression,
        arguments: &Vec<Expression>,
    ) -> std::result::Result<Object, anyhow::Error> {
        let callee = self.execute_expression(callee)?;

        let mut args = Vec::new();
        for arg in arguments {
            args.push(self.execute_expression(arg)?);
        }

        match callee {
            Object::Function(callable) => {
                if args.len() != callable.arity() {
                    return Err(anyhow!(
                        "Expected {} arguments but got {}.",
                        callable.arity(),
                        args.len()
                    ));
                }
                callable.call(self, &args)
            }
            _ => Err(anyhow!("Can only call functions and classes.")),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{parse_expression, parse_program};

    use super::*;

    fn execute_expression(input: &str) -> Result<Object> {
        let expression = parse_expression(input).expect("Error parsing expression");
        let mut interpreter = Interpreter::new(Rc::new(RefCell::new(Vec::new())));

        interpreter.execute_expression(&expression)
    }

    fn execute_program(input: &str) -> String {
        let program = parse_program(input).expect("Error parsing program");

        let buffer = Rc::new(RefCell::new(Vec::new()));
        let mut interp = Interpreter::new(buffer.clone());
        interp.evaluate(program).expect("Runtime error on test");
        let output = String::from_utf8(buffer.borrow().clone()).unwrap();

        output.trim().to_owned()
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
            assert_eq!(
                execute_expression(input).unwrap(),
                expected,
                "Input: {}",
                input
            );
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
            assert_eq!(
                execute_expression(input).unwrap(),
                expected,
                "Input: {}",
                input
            );
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
            assert_eq!(
                execute_expression(input).unwrap(),
                expected,
                "Input: {}",
                input
            );
        }
    }

    #[test]
    fn test_logical_operations() {
        let tests = vec![
            ("true or false", Object::True),
            ("false or false", Object::False),
            ("true and true", Object::True),
            ("true and false", Object::False),
            ("false or 22", Object::Number(22.0)),
            ("43 or 12", Object::Number(43.0)),
            ("false and 22", Object::False),
            ("true and 12", Object::Number(12.0)),
            ("false and false", Object::False),
            ("!true or false", Object::False),
            ("!false or true", Object::True),
        ];

        for (input, expected) in tests {
            assert_eq!(
                execute_expression(input).unwrap(),
                expected,
                "Input: {}",
                input
            );
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
            assert_eq!(
                execute_expression(input).unwrap(),
                expected,
                "Input: {}",
                input
            );
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
 
        print result;
        ";

        assert_eq!(execute_program(source), "true");

        let source = "\
        var number1 = 43;
        var number2 = 21;
        var result = false;

        if (number2 + number1 > 100) {
            result = true;
        }
 
        print result;
        ";

        assert_eq!(execute_program(source), "false");

        let source = r#"
        var result;

        if (2 + 2 * 6 == 24)
            result = "wrong";
        else
            result = "right";
 
        print result;
        "#;

        assert_eq!(execute_program(source), "right");
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

        print sum;
        ";

        assert_eq!(execute_program(source), "55");
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

        print a;
        ";

        assert_eq!(execute_program(source), "10946");

        let source = "\
        var a = 0;
        var i = 0;

        for (; i < 10;) {
            a = a + i;
            i = i + 1;
        }
        print a;
        ";
        assert_eq!(execute_program(source), "45");

        let source = r#"
        var quz = "before";

        for (var quz = 0; quz < 1; quz = quz + 1) {
            print quz;
            var quz = -1;
            print quz;
        }

        print quz;
        "#;

        let output = execute_program(source);
        assert_eq!(output, "0\n-1\nbefore");
    }

    #[test]
    fn test_evaluate_errors() {
        let tests = vec![
            (
                "\"hello\" - \"world\";",
                "Binary '-' can only be applied to numbers",
            ),
            ("5 / 0;", "Division by zero is not allowed"),
            (
                "37 + \"foo\" + 47;",
                "Binary '+' can only be applied to numbers or concatenated with strings",
            ),
            (
                "true >= false;",
                "Binary '>=' can only be applied to numbers",
            ),
            ("\"hello\"();", "Can only call functions and classes."),
            ("var time = clock(20);", "Expected 0 arguments but got 1."),
            (
                "\"hello\" + 5;",
                "Binary '+' can only be applied to numbers or concatenated with strings",
            ),
        ];

        for (input, expected_err) in tests {
            let program = parse_program(input).expect("Error parsing program");

            let mut interp = Interpreter::new(Rc::new(RefCell::new(Vec::new())));
            let result = interp.evaluate(program);

            assert!(result.is_err(), "Program {} should be an error", input);
            assert_eq!(
                result.unwrap_err().to_string(),
                expected_err,
                "Input: {}",
                input
            );
        }
    }

    #[test]
    fn test_native_functions() {
        let source = "\
        var time = clock();
        var result = time > 0;
        print result;
        ";

        let result = execute_program(source);
        assert_eq!(result, "true");

        let source = "\
        var str = \"hello\" + str(123);
        print str;
        ";

        let result = execute_program(source);
        assert_eq!(result, "hello123");
    }

    #[test]
    fn test_basic_function_return() {
        // Test a simple function with a return value
        let source = r#"
        fun add(a, b) {
            return a + b;
        }
        
        print add(5, 3);
        "#;

        let result = execute_program(source);
        assert_eq!(result, "8");
    }

    #[test]
    fn test_early_return() {
        // Test that code after a return statement is not executed
        let source = r#"
        fun earlyReturn() {
            return "early";
            print "This should not be printed";
            return "late";
        }
        
        print earlyReturn();
        "#;

        let result = execute_program(source);
        assert_eq!(result, "early");
    }

    #[test]
    fn test_implicit_nil_return() {
        // Test that functions without explicit return statements return nil and print
        let source = r#"
        fun noReturn() {
            print "No explicit return";
        }
        
        print noReturn();
        "#;

        let result = execute_program(source);
        assert_eq!(result, "No explicit return\nnil");
    }

    #[test]
    fn test_return_in_if_statement() {
        // Test return in if/else branches
        let source = r#"
        fun testIfReturn(condition) {
            if (condition) {
                return "from_if";
            } else {
                return "from_else";
            }
            return "never_reaches_here";
        }
        
        print testIfReturn(true);
        print testIfReturn(false);
        "#;

        let result = execute_program(source);
        assert_eq!(result, "from_if\nfrom_else");
    }

    #[test]
    fn test_return_in_while_loop() {
        // Test early return from a while loop
        let source = r#"
        fun testWhileReturn(n) {
            var i = 0;
            while (i < 10) {
                if (i == n) {
                    return "while_returned_at_" + str(i);
                }
                i = i + 1;
            }
            return "while_completed";
        }
        
        print testWhileReturn(5);
        print testWhileReturn(20);
        "#;

        let result = execute_program(source);
        assert_eq!(result, "while_returned_at_5\nwhile_completed");
    }

    #[test]
    fn test_return_in_for_loop() {
        // Test early return from a for loop
        let source = r#"
        fun testForReturn(n) {
            for (var i = 0; i < 10; i = i + 1) {
                if (i == n) {
                    return "for_returned_at_" + str(i);
                }
            }
            return "for_completed";
        }
        
        print testForReturn(3);
        print testForReturn(20);
        "#;

        let result = execute_program(source);
        assert_eq!(result, "for_returned_at_3\nfor_completed");
    }

    #[test]
    fn test_return_in_nested_blocks() {
        // Test return in deeply nested blocks and control structures
        let source = r#"
        fun testNestedReturn(n) {
            var result = "start";
            {
                if (n > 5) {
                    {
                        while (n > 0) {
                            if (n == 7) {
                                return "nested_return_at_" + str(n);
                            }
                            n = n - 1;
                        }
                    }
                } else {
                    for (var i = 0; i < n; i = i + 1) {
                        if (i == 3) {
                            return "nested_loop_return";
                        }
                    }
                }
            }
            return "no_early_return";
        }
        
        print testNestedReturn(9);
        print testNestedReturn(2);
        print testNestedReturn(5);
        "#;

        let result = execute_program(source);
        assert_eq!(
            result,
            "nested_return_at_7\nno_early_return\nnested_loop_return"
        );
    }
}

use std::cell::RefCell;
use std::env;
use std::fs;
use std::io;
use std::rc::Rc;

use interpreter_starter_rust::ast::Expression;
use interpreter_starter_rust::ast::Program;
use interpreter_starter_rust::interpreter::evaluator::Interpreter;
use interpreter_starter_rust::lexer::Lexer;
use interpreter_starter_rust::parser::parse_expression;
use interpreter_starter_rust::parser::parse_program;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "Usage: {} [tokenize | parse | evaluate | run] <filename>",
            args[0]
        );
        return;
    }

    let command = &args[1];
    let filename = &args[2];

    let file_contents =
        fs::read_to_string(filename).unwrap_or_else(|_| panic!("Failed to read file {}", filename));

    match command.as_str() {
        "tokenize" => {
            let lexer = Lexer::new(&file_contents);
            let tokens: Vec<_> = lexer.iter().collect();

            let mut had_lexical_error = false;

            for token in tokens {
                match token {
                    Ok(token) => println!("{}", token),
                    Err(e) => {
                        had_lexical_error = true;
                        eprintln!("{}", e);
                    }
                }
            }

            println!("EOF  null");

            if had_lexical_error {
                std::process::exit(65);
            }
        }
        "parse" => {
            let expr = parse_expression_or_exit(&file_contents);
            println!("{}", expr);
        }
        "evaluate" => {
            let expression = parse_expression_or_exit(&file_contents);
            let mut interpreter = Interpreter::new(Rc::new(RefCell::new(io::stdout())));

            match interpreter.execute_expression(&expression) {
                Ok(result) => {
                    println!("{}", result);
                }
                Err(e) => {
                    eprintln!("{}", e);
                    std::process::exit(70);
                }
            }
        }
        "run" => {
            let program = parse_program_or_exit(&file_contents);
            let mut interpreter = Interpreter::new(Rc::new(RefCell::new(io::stdout())));

            if let Err(e) = interpreter.evaluate(program) {
                eprintln!("{}", e);
                std::process::exit(70);
            }
        }
        _ => {
            eprintln!("Unknown command: {}", command);
        }
    }
}

fn parse_expression_or_exit(input: &str) -> Expression {
    match parse_expression(input) {
        Ok(expression) => expression,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(65);
        }
    }
}

fn parse_program_or_exit(input: &str) -> Program {
    match parse_program(input) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(65);
        }
    }
}

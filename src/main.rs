use std::env;
use std::fs;

use interpreter_starter_rust::ast::Program;
use interpreter_starter_rust::interpreter::evaluator::Interpreter;
use interpreter_starter_rust::lexer::Lexer;
use interpreter_starter_rust::parser::parse_program;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} tokenize <filename>", args[0]);
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
            let program = parse_program_or_exit(&file_contents);
            for stmt in program.statements {
                println!("{}", stmt);
            }
        }
        "evaluate" | "run" => {
            let program = parse_program_or_exit(&file_contents);
            let mut interpreter = Interpreter::new();

            match interpreter.evaluate(program) {
                Ok(Some(result)) => {
                    if command == "evaluate" {
                        println!("{}", result);
                    }
                }
                Ok(None) => {}
                Err(e) => {
                    eprintln!("{}", e);
                    std::process::exit(70);
                }
            }
        }
        _ => {
            eprintln!("Unknown command: {}", command);
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

use std::env;
use std::fs;

use interpreter_starter_rust::interpreter::evaluator::evaluate;
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
        "parse" => match parse_program(&file_contents) {
            Ok(program) => {
                for stmt in program.statements {
                    println!("{}", stmt);
                }
            }
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(65);
            }
        },
        "evaluate" => match parse_program(&file_contents)
            .map_err(|e| e.into())
            .and_then(|program| evaluate(program))
        {
            Ok(result) => println!("{}", result),
            Err(e) => {
                eprintln!("{}", e);
                std::process::exit(65);
            }
        },
        _ => {
            eprintln!("Unknown command: {}", command);
        }
    }
}

use std::env;
use std::fs;

use interpreter_starter_rust::lexer::Lexer;
use interpreter_starter_rust::parser::Parser;

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
                    Ok(token) => println!("{:?}", token),
                    Err(e) => {
                        had_lexical_error = true;
                        eprintln!("{}", e);
                    }
                }
            }

            if had_lexical_error {
                std::process::exit(65);
            }
        }
        "parse" => {
            let lexer = Lexer::new(&file_contents);
            let mut parser = Parser::new(lexer);

            match parser.parse() {
                Ok(program) => {
                    for stmt in program.statements {
                        println!("{}", stmt);
                    }
                }
                Err(e) => panic!("{}", e),
            }
        }
        _ => {
            eprintln!("Unknown command: {}", command);
        }
    }
}

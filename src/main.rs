mod ast;
mod bitvector;
mod lexer;
mod parser;
mod sat;
mod solver;

use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut smt = solver::SmtSolver::new();

    if args.len() > 1 {
        // File mode: read and process an SMT-LIB file
        let filename = &args[1];
        match fs::read_to_string(filename) {
            Ok(contents) => match smt.process_input(&contents) {
                Ok(responses) => {
                    for r in responses {
                        println!("{}", r);
                    }
                }
                Err(e) => {
                    eprintln!("Error: {}", e);
                    std::process::exit(1);
                }
            },
            Err(e) => {
                eprintln!("Error reading file '{}': {}", filename, e);
                std::process::exit(1);
            }
        }
    } else {
        // Interactive mode: read from stdin
        smt.run_interactive();
    }
}

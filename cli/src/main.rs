use std::{fmt::Display, path::PathBuf, time::Instant};

use colored::Colorize;

fn display_err(text: impl Display) {
    eprintln!("{} {}", "error:".red().bold(), text)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 1 {
        return display_err("wrong number of arguments. Usage: ./erl_cli <file>");
    }

    let file_name = &args[0];
    let file_path = PathBuf::from(file_name);
    if !file_path.exists() {
        return display_err(format_args!("File `{file_name}` does not exist"));
    }

    let file = match erl_parser::file::File::read(file_path) {
        Ok(file) => file,
        Err(err) => return display_err(format_args!("Failed to read `{file_name}`: {err}")),
    };

    let ast = match erl_parser::parse_program(file) {
        Ok(ast) => ast,
        Err(errs) => {
            display_err(format_args!(
                "could not parse {file_name} due to {} syntax {}",
                errs.len(),
                if errs.len() > 1 { "errors" } else { "error" }
            ));
            eprintln!();
            for err in errs {
                eprintln!("{}", err);
            }
            return;
        }
    };

    let module = erl_bytecode_exec::compiler::compile(ast);
    if args.contains(&String::from("--emit-bytecode")) {
        println!("{module:#?}");
        println!("Now executing:");
    }

    let before = Instant::now();
    match erl_bytecode_exec::executor::execute(&module) {
        Ok(_) => {}
        Err(err) => display_err(err),
    };

    if args.contains(&String::from("--time")) {
        let time_taken = Instant::now().duration_since(before).as_secs_f64();

        println!("Finished. Took: {time_taken}s");
    }
}

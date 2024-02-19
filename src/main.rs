mod api;
mod lang;
mod ui;

#[macro_use]
extern crate log;

use crate::{
    api::cli::{Arguments, UI},
    lang::lexer::Lexer,
    lang::parser::Parser,
};
use clap::Parser as _;
use colored::Colorize;
use std::io::Write;

fn main() {
    let args = Arguments::parse();
    if args.version {
        print_version();
        return;
    }

    // Get source file path.
    let path = args.file.clone().unwrap_or_else(|| {
        let exe_dir = std::env::current_exe()
            .unwrap()
            .parent()
            .unwrap()
            .to_path_buf();
        println!("Error: `{}` is required.", "--file <PATH>".bold());
        print!("Or input the path relative to the executable: ");
        std::io::stdout().flush().unwrap();
        let mut path = String::default();
        std::io::stdin().read_line(&mut path).unwrap();
        let path = exe_dir.join(path.trim());
        let path = path.to_str().unwrap_or_else(|| {
            println!("Error: Invalid path.");
            std::process::exit(1);
        });
        path.to_string()
    });

    // Initialize logger.
    if log4rs::init_file(
        "config/log4rs.yaml",
        log4rs::config::Deserializers::default(),
    )
    .is_err()
    {
        println!("Failed to load log configuration. Log would be disabled.");
    }
    debug!("Program start up with args: {:?}", args);
    info!("Log loaded to `./instance/run.[#].log`.");

    // Read source file.
    debug!("Load source file from `{:?}`.", path);
    let src = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        println!(
            "{}",
            format!("Error: Failed to read source file: {}", e).red()
        );
        std::process::exit(1);
    });
    debug!("Source code:\n{src}\n");

    // Lex / tokenize
    let (tokens, lex_errors) = Lexer::with_source(&src).lex_effective();
    assert_errors_empty("Lexing", lex_errors);
    debug!("Tokens: {:#?}", tokens);

    // Parse
    let (statements, parse_errors) = Parser::with_tokens(tokens).parse_effective();
    assert_errors_empty("Parsing", parse_errors);
    debug!("Statements: {:#?}", statements);

    match match args.ui {
        UI::Tui => ui::tui::main,
        UI::Gui => ui::gui::main,
    }(path.to_string(), statements)
    {
        Ok(_) => {}
        Err(e) => {
            error!("UI exited with error: {}", e);
            std::process::exit(1);
        }
    }
}

fn print_version() {
    if let Some(version) = option_env!("CARGO_PKG_VERSION") {
        println!("DszL Interpreter {version}");
    } else {
        println!("DszL Interpreter");
    }

    if let Some(author) = option_env!("CARGO_PKG_AUTHORS") {
        println!("Copyright (C) 2024 {author}");
    }

    if let Some(source) = option_env!("CARGO_PKG_REPOSITORY") {
        if !source.is_empty() {
            println!("Source available at {source}");
        }
    }
}

fn assert_errors_empty(typ: &str, errors: Vec<impl std::fmt::Display>) {
    if !errors.is_empty() {
        error!("{} failed with {} error(s).", typ, errors.len());
        for e in errors {
            error!("{}", e);
        }
        error!("Aborting.");
        std::process::exit(1);
    }
}

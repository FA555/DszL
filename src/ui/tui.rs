use crate::{
    api::interact::Interact,
    lang::{result::ExecError, statement::Statement, visitor::Visitor},
};
use colored::Colorize;
use std::{io::Write, sync::Arc};

/// `TuiInteractor` is a struct implementing the `Interact` trait for a text-based user interface.
///
/// It provides methods to handle input and output operations in a TUI environment.
pub(crate) struct TuiInteractor;

impl TuiInteractor {
    /// Constructs a new `TuiInteractor`.
    ///
    /// # Returns
    ///
    /// - `TuiInteractor`: A new instance of `TuiInteractor`.
    pub(crate) fn new() -> Self {
        Self
    }
}

/// The default implementation of `TuiInteractor`.
impl Default for TuiInteractor {
    /// Constructs a new `TuiInteractor`.
    fn default() -> Self {
        Self::new()
    }
}

impl Interact for TuiInteractor {
    /// Requests and retrieves user input as a string in a TUI environment.
    ///
    /// This method prompts the user for input and blocks until input is received.
    ///
    /// # Returns
    ///
    /// - `String`: The user's input.
    fn input(&self) -> String {
        print!("├─ ");
        std::io::stdout().flush().unwrap();

        let mut s = String::default();
        std::io::stdin().read_line(&mut s).unwrap();
        s
    }

    /// Requests and retrieves user input with a timeout in a TUI environment.
    ///
    /// This method prompts the user for input and blocks until input is received or the timeout is reached.
    ///
    /// # Arguments
    ///
    /// - `duration`: The maximum duration to wait for user input.
    ///
    /// # Returns
    ///
    /// - `Option<String>`: The user's input if provided before the timeout, or `None` if the timeout is reached.
    fn input_timeout(&self, duration: std::time::Duration) -> Option<String> {
        print!("├─ ");
        std::io::stdout().flush().unwrap();

        let mut rset: libc::fd_set = unsafe { std::mem::zeroed() };
        unsafe {
            libc::FD_SET(0, &mut rset);
        }
        let mut tv = libc::timeval {
            tv_sec: duration.as_secs() as libc::time_t,
            tv_usec: duration.subsec_micros() as libc::suseconds_t,
        };
        let ret = unsafe {
            libc::select(
                1,
                &mut rset,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                &mut tv,
            )
        };

        match ret {
            0 => None,
            1 => {
                let mut s = String::default();
                std::io::stdin().read_line(&mut s).unwrap();
                Some(s)
            }
            _ => panic!("select() failed with return value {}", ret),
        }
    }

    /// Outputs the given string to the TUI.
    ///
    /// This method processes and displays the string in the TUI, handling special markers for line feeds and tabs.
    ///
    /// # Arguments
    ///
    /// - `s`: The string to be outputted.
    fn output(&self, s: &str) {
        let mut s = s;
        if s.starts_with("[[LF]]") {
            println!();
            s = &s[6..];
        }
        let s = s.replace("[[LF]]", "\n").replace("[[TAB]]", "\t");
        for line in s.lines() {
            println!("{}", format!("│  {line}").blue());
        }
    }
}

/// The entry point of the application running with a Text-Based User Interface (TUI).
///
/// This function initializes the TUI Interactor and starts executing the provided statements.
///
/// # Arguments
///
/// - `file`: The name of the file being executed.
/// - `statements`: A vector of statements to be executed by the interpreter.
///
/// # Returns
///
/// - `std::io::Result<()>`: Result indicating the success or failure of the application startup and execution.
pub(crate) fn main(file: String, statements: Vec<Statement>) -> std::io::Result<()> {
    info!("TUI start up with file `{}`.", file);
    match Visitor::with_interactor(Arc::new(TuiInteractor::default())).executes(statements) {
        Ok(_) | Err(ExecError::Exit) => Ok(()),
        Err(e) => {
            error!("Execution failed with error: {}", e);
            std::process::exit(1);
        }
    }
}

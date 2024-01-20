pub(crate) mod result;

pub(crate) mod lexer;
mod token;

mod environment;
mod expr;
pub(crate) mod parser;
pub(crate) mod statement;
mod variable;
pub(crate) mod visitor;
// mod parser;

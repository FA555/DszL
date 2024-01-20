use crate::lang::{expr::Expr, result::ExecResult, token::Token};

#[derive(Clone, Debug)]
pub(crate) struct TimeoutAction {
    pub(crate) duration: Expr,
    pub(crate) action: Box<Statement>,
}

/// Represents the different kinds of statements that can appear in the language. A statement is an executable unit of
/// code that performs an action, such as declaring variables, executing expressions, controlling flow, and more. Each
/// variant in this enum encapsulates a specific type of statement, along with any relevant data it needs.
#[derive(Clone, Debug)]
pub(crate) enum Statement {
    /// A block of statements, typically enclosed in braces. Used to group multiple statements.
    Block(Vec<Statement>),
    /// Represents an exit statement, used to terminate the program or exit from a block.
    Exit,
    /// A statement that consists solely of an expression.
    Expression(Expr),
    /// Represents a state declaration with an identifier, parameters, and a body consisting of statements.
    State {
        ident: Token,
        params: Vec<Token>,
        body: Vec<Statement>,
    },
    /// An `if` statement with a condition expression, a then branch, and an optional else branch.
    If {
        condition: Expr,
        then_branch: Box<Statement>,
        else_branch: Option<Box<Statement>>,
    },
    /// An input statement for reading a line of text into the specified variable.
    Input {
        ident: Token,
        timeout_action: Option<TimeoutAction>,
    },
    /// An input statement specifically for reading a numerical value into the specified variable.
    InputNum {
        ident: Token,
        timeout_action: Option<TimeoutAction>,
    },
    /// An output statement for printing an expression to the standard output.
    Output(Expr),
    /// A sleep statement for pausing execution for a duration specified by the expression.
    Sleep(Expr),
    /// A let statement for variable declaration and optional initialization.
    Let {
        ident: Token,
        initialiser: Option<Expr>,
    },
    /// A while statement for representing loops. Currently, its condition part is commented out.
    While {
        condition: Expr,
        body: Box<Statement>,
    },
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Statement::Block(statements) => {
                let mut s = String::from("{ ");
                for statement in statements {
                    s = format!("{}{} ", s, statement);
                }
                write!(f, "{}}}", s)
            }
            Statement::Exit => write!(f, "exit;"),
            Statement::Expression(expr) => write!(f, "[Expr: {}];", expr),
            Statement::State {
                ident,
                params,
                body,
            } => {
                let mut s = format!("state [Ident: {}](", ident.lexeme);
                for param in params {
                    s = format!("{}[Ident: {}] ", s, param.lexeme);
                }
                s = format!("{}) {{ ", s);
                for statement in body {
                    s = format!("{}{} ", s, statement);
                }
                write!(f, "{}}}", s)
            }
            Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut s = format!("if ({}) {}", condition, then_branch);
                if let Some(else_branch) = else_branch {
                    s = format!("{} else {}", s, else_branch);
                }
                write!(f, "{}", s)
            }
            Statement::Input {
                ident,
                timeout_action,
            } => {
                write!(f, "input [Ident: {}", ident.lexeme)?;
                if let Some(TimeoutAction { duration, action }) = &timeout_action {
                    write!(f, " timeout [Expr: {}] action {}", duration, action)?;
                }
                write!(f, "];")
            }
            Statement::InputNum {
                ident,
                timeout_action,
            } => {
                write!(f, "input_num [Ident: {}", ident.lexeme)?;
                if let Some(TimeoutAction { duration, action }) = &timeout_action {
                    write!(f, " timeout [Expr: {}] action {}", duration, action)?;
                }
                write!(f, "];")
            }
            Statement::Output(expr) => write!(f, "output [Expr: {}];", expr),
            Statement::Sleep(expr) => write!(f, "sleep [Expr: {}];", expr),
            Statement::Let { ident, initialiser } => {
                let mut s = format!("let [Ident: {}]", ident.lexeme);
                if let Some(initialiser) = initialiser {
                    s = format!("{} = {};", s, initialiser);
                }
                write!(f, "{}", s)
            }
            Statement::While { condition, body } => write!(f, "while ({}) {}", condition, body),
        }
    }
}

/// Allows `Statement` instances to be processed by different types of visitors, each potentially performing different
/// operations on the statements. This design follows the Visitor Pattern, enabling operations to be defined outside
/// the `Statement` class hierarchy. It's useful in scenarios like code generation, optimization, and interpretation.
impl Statement {
    pub(crate) fn dispatch_visit<T>(
        &self,
        visitor: &mut impl StatementVisitor<T>,
    ) -> ExecResult<T> {
        match &self {
            Statement::Block(_) => visitor.visit_block(self),
            Statement::Exit => visitor.visit_exit(self),
            Statement::Expression(_) => visitor.visit_expression(self),
            Statement::State { .. } => visitor.visit_function(self),
            Statement::If { .. } => visitor.visit_if(self),
            Statement::Input { .. } => visitor.visit_input(self),
            Statement::InputNum { .. } => visitor.visit_input_num(self),
            // Statement::Null => visitor.visit_null(self),
            Statement::Output(_) => visitor.visit_output(self),
            Statement::Sleep(_) => visitor.visit_sleep(self),
            Statement::Let { .. } => visitor.visit_let(self),
            Statement::While { .. } => visitor.visit_while(self),
        }
    }
}

/// A trait for visiting statements (`Statement`). Implementors of this trait can provide specific logic for handling
/// different types of statements. It's part of the Visitor Pattern, allowing various operations to be applied to
/// statements, such as evaluation, transformation, or printing.
pub(crate) trait StatementVisitor<T> {
    fn visit_block(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_exit(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_expression(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_function(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_if(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_input(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_input_num(&mut self, statement: &Statement) -> ExecResult<T>;
    // fn visit_null(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_output(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_sleep(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_let(&mut self, statement: &Statement) -> ExecResult<T>;
    fn visit_while(&mut self, statement: &Statement) -> ExecResult<T>;
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lang::{expr::Value, token::TokenType};

    #[test]
    fn statement_display() {
        let statement = Statement::Block(vec![
            Statement::Let {
                ident: Token::new(TokenType::Identifier, "x", 1),
                initialiser: Some(Expr::Literal(Value::Number(1.0))),
            },
            Statement::Let {
                ident: Token::new(TokenType::Identifier, "y", 1),
                initialiser: Some(Expr::Literal(Value::Number(1.0))),
            },
            Statement::Let {
                ident: Token::new(TokenType::Identifier, "z", 1),
                initialiser: Some(Expr::Literal(Value::Number(1.0))),
            },
            Statement::Expression(Expr::Binary {
                lhs: Box::new(Expr::Variable(Token::new(TokenType::Identifier, "x", 1))),
                op: Token::new(TokenType::Plus, "+", 1),
                rhs: Box::new(Expr::Binary {
                    lhs: Box::new(Expr::Variable(Token::new(TokenType::Identifier, "y", 2))),
                    op: Token::new(TokenType::Minus, "-", 1),
                    rhs: Box::new(Expr::Variable(Token::new(TokenType::Identifier, "z", 3))),
                }),
            }),
        ]);
        assert_eq!(
            statement.to_string(),
            "{ let [Ident: x] = [Literal 1]; let [Ident: y] = [Literal 1]; let [Ident: z] = [Literal 1]; [Expr: [Binary + [Variable x] [Binary - [Variable y] [Variable z]]]]; }"
        );
    }
}

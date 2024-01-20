use crate::lang::{result::ExecResult, token::Token};

/// Represents the possible values that can be produced by evaluating expressions in the language.
/// This enum encapsulates various types of values, such as booleans, numbers, strings, and a special
/// `Nil` value to represent the absence of a value.
#[derive(Debug, Clone)]
pub(crate) enum Value {
    /// Represents a boolean value (`true` or `false`).
    Boolean(bool),
    /// Represents the absence of a value.
    Nil,
    /// Represents a numeric value, stored as a floating-point number.
    Number(f64),
    /// Represents a string value.
    Str(String),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Value::Boolean(b) => write!(f, "{}", b),
            Value::Nil => write!(f, "nil"),
            Value::Number(n) => write!(f, "{}", n),
            Value::Str(s) => write!(f, "\"{}\"", s),
        }
    }
}

/// Represents an expression in the language. Expressions can be assignments, binary operations,
/// function calls, literals, unary operations, and variable references. Each variant of `Expr`
/// is designed to hold the necessary information to represent and evaluate the expression.
#[derive(Debug, Clone)]
pub(crate) enum Expr {
    /// Represents an assignment expression with a left-hand side (lhs) variable name and a right-hand side (rhs)
    /// expression.
    Assign { lhs: Token, rhs: Box<Expr> },
    /// Represents a binary operation with left-hand side (lhs) and right-hand side (rhs) expressions and an operator
    /// token.
    Binary {
        lhs: Box<Expr>,
        op: Token,
        rhs: Box<Expr>,
    },
    /// Represents a function call with the function expression and a vector of argument expressions.
    Call { func: Box<Expr>, args: Vec<Expr> },
    /// Represents a literal value.
    Literal(Value),
    /// Represents a unary operation with an operator token and a right-hand side (rhs) expression.
    Unary { op: Token, rhs: Box<Expr> },
    /// Represents a variable reference with a token containing the variable's name.
    Variable(Token),
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Expr::Assign { lhs, rhs } => write!(f, "[Assign {} <- {}]", lhs, rhs),
            Expr::Binary { lhs, op, rhs } => write!(f, "[Binary {} {} {}]", op.lexeme, lhs, rhs),
            Expr::Call { func, args } => {
                let mut s = format!("[Call {}", func);
                if !args.is_empty() {
                    s = format!("{} with", s);
                }
                for arg in args {
                    s = format!("{} {}", s, arg);
                }
                write!(f, "{}]", s)
            }
            Expr::Literal(v) => write!(f, "[Literal {}]", v),
            Expr::Unary { op, rhs } => write!(f, "[Unary {} {}]", op.lexeme, rhs),
            Expr::Variable(v) => write!(f, "[Variable {}]", v.lexeme),
        }
    }
}

/// Allows `Expr` instances to be processed by different types of visitors, each potentially performing different
/// operations on the expressions. This design follows the Visitor Pattern, enabling operations to be defined outside
/// the `Expr` class hierarchy. It's particularly useful in scenarios like expression evaluation, transformation, and
/// serialisation.
impl Expr {
    pub(crate) fn dispatch_visit<T>(&self, visitor: &mut impl ExprVisitor<T>) -> ExecResult<T> {
        match self {
            Expr::Assign { .. } => visitor.visit_assign(self),
            Expr::Binary { .. } => visitor.visit_binary(self),
            Expr::Call { .. } => visitor.visit_call(self),
            Expr::Literal(_) => visitor.visit_literal(self),
            Expr::Unary { .. } => visitor.visit_unary(self),
            Expr::Variable(_) => visitor.visit_variable(self),
        }
    }
}

/// A trait for visiting expressions (`Expr`). This trait should be implemented by any type that intends to process
/// expressions, providing specific logic for each kind of expression. It's part of the Visitor Pattern, allowing
/// different operations to be applied to expressions.
///
/// Each method corresponds to a variant of `Expr`, allowing the visitor to handle each expression type accordingly.
pub(crate) trait ExprVisitor<T> {
    fn visit_assign(&mut self, expr: &Expr) -> ExecResult<T>;
    fn visit_binary(&mut self, expr: &Expr) -> ExecResult<T>;
    fn visit_call(&mut self, expr: &Expr) -> ExecResult<T>;
    fn visit_literal(&mut self, expr: &Expr) -> ExecResult<T>;
    fn visit_unary(&mut self, expr: &Expr) -> ExecResult<T>;
    fn visit_variable(&mut self, expr: &Expr) -> ExecResult<T>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::token::TokenType;

    #[test]
    fn expr_display() {
        let expr = Expr::Literal(Value::Number(1.0));
        assert_eq!(format!("{}", expr), "[Literal 1]");

        let expr = Expr::Literal(Value::Boolean(true));
        assert_eq!(format!("{}", expr), "[Literal true]");

        let expr = Expr::Literal(Value::Nil);
        assert_eq!(format!("{}", expr), "[Literal nil]");

        let expr = Expr::Literal(Value::Str("Hello, world!".to_string()));
        assert_eq!(format!("{}", expr), "[Literal \"Hello, world!\"]");

        let expr = Expr::Variable(Token::new(TokenType::Identifier, "my_var", 1));
        assert_eq!(format!("{}", expr), "[Variable my_var]");

        let expr = Expr::Unary {
            op: Token::new(TokenType::Minus, "-", 1),
            rhs: Box::new(Expr::Literal(Value::Number(1.0))),
        };
        assert_eq!(format!("{}", expr), "[Unary - [Literal 1]]");

        let expr = Expr::Binary {
            lhs: Box::new(Expr::Literal(Value::Number(1.0))),
            op: Token::new(TokenType::Plus, "+", 1),
            rhs: Box::new(Expr::Literal(Value::Number(2.0))),
        };
        assert_eq!(format!("{}", expr), "[Binary + [Literal 1] [Literal 2]]");

        let expr = Expr::Call {
            func: Box::new(Expr::Variable(Token::new(
                TokenType::Identifier,
                "my_func",
                1,
            ))),
            args: vec![
                Expr::Literal(Value::Number(1.0)),
                Expr::Literal(Value::Number(2.0)),
            ],
        };
        assert_eq!(
            format!("{}", expr),
            "[Call [Variable my_func] with [Literal 1] [Literal 2]]"
        );

        let expr = Expr::Assign {
            lhs: Token::new(TokenType::Identifier, "my_var", 1),
            rhs: Box::new(Expr::Literal(Value::Number(1.0))),
        };
        assert_eq!(
            format!("{}", expr),
            "[Assign Identifier my_var <- [Literal 1]]"
        );
    }
}

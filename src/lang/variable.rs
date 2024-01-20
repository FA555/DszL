use crate::lang::{
    environment::Environment, expr::Value, result::ExecResult, statement::Statement, token::Token,
    visitor::Visitor,
};
use std::{cell::RefCell, rc::Rc};

/// Represents a function within the language written by the user containing custom logic.
#[derive(Clone, Debug)]
pub(crate) struct Function {
    /// Identifier token of the function.
    #[allow(unused)]
    ident: Token,
    /// Vector of parameter tokens.
    params: Vec<Token>,
    /// Vector of statements representing the body of the function.
    body: Vec<Statement>,
    /// Reference to the environment in which the function is defined.
    env: Rc<RefCell<Environment>>,
}

impl Function {
    /// Creates a new function with the given identifier, parameter tokens, body statements, and environment.
    /// This is typically used for user-defined functions.
    pub(crate) fn with_params(
        ident: Token,
        params: Vec<Token>,
        body: Vec<Statement>,
        env: Rc<RefCell<Environment>>,
    ) -> Self {
        Self {
            ident,
            params,
            body,
            env,
        }
    }

    /// Calls the function with a set of arguments and returns the result. For built-in functions, it directly invokes
    /// the function pointer. For user-defined functions, it creates a new environment, sets up parameters, and
    /// executes the body.
    ///
    /// # Arguments
    ///
    /// - `visitor`: The visitor to use for executing user-defined functions.
    /// - `args`: The arguments to pass to the function.
    ///
    /// # Returns
    ///
    /// `ExecResult<Variable>` - The result of the function call.
    pub(crate) fn call(&self, visitor: &mut Visitor, args: &[Variable]) -> ExecResult<Variable> {
        let env = Rc::new(RefCell::new(Environment::derive(&self.env)));
        for (param, arg) in self.params.iter().zip(args) {
            env.borrow_mut().define_variable(&param.lexeme, arg.clone());
        }
        match visitor.executes_with_env(&self.body, env) {
            Ok(_) => Ok(Variable::Nil),
            Err(e) => Err(e),
        }
    }

    /// Returns the number of parameters that the function accepts.
    ///
    /// # Returns
    ///
    /// `usize` - The number of parameters.
    pub(crate) fn accept_param_amount(&self) -> usize {
        self.params.len()
    }
}

/// Represents a variable in the language. Variables can hold different types of values, such as booleans, numbers,
/// strings, and callable functions.
#[derive(Clone, Debug)]
pub(crate) enum Variable {
    Boolean(bool),
    Callable(Function),
    Nil,
    Number(f64),
    Str(String),
}

/// Implementation of the `PartialEq` trait for `Variable`, providing a way to compare two variables for equality. This
/// is essential for implementing comparison operations within the language.
impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Variable::Boolean(b1), Variable::Boolean(b2)) => b1 == b2,
            (Variable::Nil, Variable::Nil) => true,
            (Variable::Number(n1), Variable::Number(n2)) => n1 == n2,
            (Variable::Str(s1), Variable::Str(s2)) => s1 == s2,
            _ => false,
        }
    }
}

impl std::fmt::Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Variable::Boolean(b) => write!(f, "{}", b),
            Variable::Callable(_) => write!(f, "<callable>"),
            Variable::Nil => write!(f, "nil"),
            Variable::Number(n) => write!(f, "{}", n),
            Variable::Str(s) => write!(f, "{}", s),
        }
    }
}

impl Variable {
    /// Converts a `Value` into a `Variable`. This is a utility function to bridge between the expression evaluation
    /// results (`Value`) and the variables used in the language.
    ///
    /// # Arguments
    ///
    /// - `value`: The value to convert into a variable.
    ///
    /// # Returns
    ///
    /// `Variable` - The resulting variable.
    pub(crate) fn from_value(value: Value) -> Self {
        match value {
            Value::Boolean(b) => Variable::Boolean(b),
            Value::Nil => Variable::Nil,
            Value::Number(n) => Variable::Number(n),
            Value::Str(s) => Variable::Str(s),
        }
    }

    // Arithmetic and comparison methods (add, sub, eq, ne, lt, le, gt, ge, neg, is_truthy, not)

    /// Performs addition operation on two variables. This is typically used for numeric addition or string
    /// concatenation, depending on the types of the variables.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of addition, or `None` if the operation is not valid.
    pub(crate) fn add(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match (lhs, rhs) {
            (Variable::Number(n1), Variable::Number(n2)) => Some(Variable::Number(n1 + n2)),
            (Variable::Str(s), rhs) => Some(Variable::Str(format!("{}{}", s, rhs))),
            (lhs, Variable::Str(s)) => Some(Variable::Str(format!("{}{}", lhs, s))),
            _ => None,
        }
    }

    /// Performs subtraction operation on two variables. This is typically used for numeric subtraction.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of subtraction, or `None` if the operation is not valid.
    pub(crate) fn sub(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match (lhs, rhs) {
            (Variable::Number(n1), Variable::Number(n2)) => Some(Variable::Number(n1 - n2)),
            _ => None,
        }
    }

    pub(crate) fn match_(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match (lhs, rhs) {
            (Variable::Str(s1), Variable::Str(s2)) => Some(Variable::Boolean(
                s1.contains(s2)
                    || s2.contains(s1)
                    || match regex::Regex::new(s2) {
                        Ok(re) => re.is_match(s1),
                        Err(_) => false,
                    },
            )),
            _ => None,
        }
    }

    pub(crate) fn land(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match (lhs, rhs) {
            (Variable::Boolean(b1), Variable::Boolean(b2)) => Some(Variable::Boolean(*b1 && *b2)),
            _ => None,
        }
    }

    pub(crate) fn lor(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match (lhs, rhs) {
            (Variable::Boolean(b1), Variable::Boolean(b2)) => Some(Variable::Boolean(*b1 || *b2)),
            _ => None,
        }
    }

    /// Performs equality comparison on two variables. This is typically used for numeric or string equality
    /// comparison.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of equality comparison, or `None` if the operation is not valid.
    pub(crate) fn eq(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match (lhs, rhs) {
            (Variable::Boolean(b1), Variable::Boolean(b2)) => Some(Variable::Boolean(b1 == b2)),
            (Variable::Nil, Variable::Nil) => Some(Variable::Boolean(true)),
            (Variable::Number(n1), Variable::Number(n2)) => Some(Variable::Boolean(n1 == n2)),
            (Variable::Str(s1), Variable::Str(s2)) => Some(Variable::Boolean(s1 == s2)),
            _ => None,
        }
    }

    /// Performs inequality comparison on two variables. This is typically used for numeric or string inequality
    /// comparison.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of inequality comparison, or `None` if the operation is not valid.
    pub(crate) fn ne(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match Self::eq(lhs, rhs) {
            Some(Variable::Boolean(b)) => Some(Variable::Boolean(!b)),
            _ => None,
        }
    }

    /// Performs less-than comparison on two variables. This is typically used for numeric or string less-than
    /// comparison.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of less-than comparison, or `None` if the operation is not valid.
    pub(crate) fn lt(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match (lhs, rhs) {
            (Variable::Number(n1), Variable::Number(n2)) => Some(Variable::Boolean(n1 < n2)),
            (Variable::Str(s1), Variable::Str(s2)) => Some(Variable::Boolean(s1 < s2)),
            _ => None,
        }
    }

    /// Performs less-than-or-equal comparison on two variables. This is typically used for numeric or string
    /// less-than-or-equal comparison.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of less-than-or-equal comparison, or `None` if the operation is not valid.
    pub(crate) fn le(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match Self::lt(rhs, lhs) {
            Some(Variable::Boolean(b)) => Some(Variable::Boolean(!b)),
            _ => None,
        }
    }

    /// Performs greater-than comparison on two variables. This is typically used for numeric or string greater-than
    /// comparison.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of greater-than comparison, or `None` if the operation is not valid.
    pub(crate) fn gt(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match Self::lt(rhs, lhs) {
            Some(Variable::Boolean(b)) => Some(Variable::Boolean(b)),
            _ => None,
        }
    }

    /// Performs greater-than-or-equal comparison on two variables. This is typically used for numeric or string
    /// greater-than-or-equal comparison.
    ///
    /// # Arguments
    ///
    /// - `lhs`: The left-hand side variable.
    /// - `rhs`: The right-hand side variable.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of greater-than-or-equal comparison, or `None` if the operation is not valid.
    pub(crate) fn ge(lhs: &Self, rhs: &Self) -> Option<Variable> {
        match Self::lt(lhs, rhs) {
            Some(Variable::Boolean(b)) => Some(Variable::Boolean(!b)),
            _ => None,
        }
    }

    /// Performs negation on a variable. This is typically used for numeric negation.
    ///
    /// # Arguments
    ///
    /// - `self`: The variable to negate.
    ///
    /// # Returns
    ///
    /// `Option<Variable>` - The result of negation, or `None` if the operation is not valid.
    pub(crate) fn neg(self) -> Option<Variable> {
        match self {
            Variable::Number(n) => Some(Variable::Number(-n)),
            _ => None,
        }
    }

    /// Determines if a variable is truthy. In this language, false and nil are falsy, and everything else is truthy.
    /// This method is crucial for conditional statements and logical operations.
    ///
    /// # Returns
    ///
    /// `bool` - `true` if the variable is truthy, `false` otherwise.
    pub(crate) fn is_truthy(&self) -> bool {
        match self {
            Variable::Boolean(b) => *b,
            Variable::Number(n) => *n != 0.0,
            Variable::Nil => false,
            Variable::Str(s) => !s.is_empty(),
            _ => true,
        }
    }

    /// Performs logical NOT operation on a variable. This method converts the variable into a boolean based on its
    /// truthiness and then negates it.
    ///
    /// # Returns
    /// `Option<Variable>` - The result of the NOT operation.
    pub(crate) fn not(self) -> Option<Variable> {
        Some(Variable::Boolean(!self.is_truthy()))
    }
}

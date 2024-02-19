use crate::lang::{
    result::{ExecError, ExecResult},
    token::Token,
    variable::Variable,
};
use std::{cell::RefCell, collections::HashMap, rc::Rc};

/// Represents the state of the execution environment, holding variables and their values.
/// This struct can be used to create nested scopes, with each state having an optional parent.
#[derive(Debug)]
pub(crate) struct Environment {
    /// Optional parent state for nested scopes. `None` for root state.
    pub(crate) parent: Option<Rc<RefCell<Environment>>>,
    /// A map of variable names to their corresponding `Variable` values.
    pub(crate) variables: HashMap<String, Variable>,
}

impl Environment {
    /// Creates a new root `Environment` with no parent and an empty variable map.
    ///
    /// # Returns
    ///
    /// A new `Environment` instance representing the root scope.
    pub(crate) fn root() -> Self {
        Environment {
            parent: None,
            variables: HashMap::default(),
        }
    }

    /// Derives a new `Environment` from a parent, creating a nested scope.
    ///
    /// # Arguments
    ///
    /// - `parent`: Reference to the parent `Environment`.
    ///
    /// # Returns
    ///
    /// A new `Environment` instance representing a nested scope.
    pub(crate) fn derive(parent: &Rc<RefCell<Environment>>) -> Self {
        Environment {
            parent: Some(parent.clone()),
            variables: HashMap::default(),
        }
    }

    /// Defines a new variable or updates an existing one in the current state.
    ///
    /// # Arguments
    ///
    /// - `ident`: The token representing the variable's identifier.
    /// - `value`: The value to assign to the variable.
    pub(crate) fn define_variable(&mut self, name: &str, value: Variable) {
        self.variables.insert(name.to_string(), value);
    }

    /// Accesses the value of a variable, searching the current state and parent scopes.
    ///
    /// # Arguments
    ///
    /// - `ident`: The token representing the variable's identifier.
    ///
    /// # Returns
    ///
    /// `ExecResult<Variable>` which is the value of the variable if found, or an error if the variable is not defined
    /// in the current scope or any parent scopes.
    pub(crate) fn access_variable(&self, ident: &Token) -> ExecResult<Variable> {
        let name = &ident.lexeme;
        match self.variables.get(name) {
            Some(v) => Ok(v.clone()),
            None => match &self.parent {
                Some(p) => p.borrow().access_variable(ident),
                None => Err(ExecError::VariableNotFound(
                    name.to_string(),
                    ident.line_num,
                )),
            },
        }
    }

    /// Modifies the value of an existing variable, searching the current state and parent scopes.
    ///
    /// # Arguments
    ///
    /// - `ident`: The token representing the variable's identifier.
    /// - `value`: The new value to assign to the variable.
    ///
    /// # Returns
    ///
    /// `ExecResult<()>` which is `Ok(())` if the variable is successfully modified, or an error if the variable is not
    /// found in the current scope or any parent scopes.
    pub(crate) fn modify_variable(&mut self, ident: &Token, value: Variable) -> ExecResult<()> {
        let name = &ident.lexeme;
        match self.variables.get_mut(name) {
            Some(v) => {
                *v = value;
                Ok(())
            }
            None => match &self.parent {
                Some(p) => p.borrow_mut().modify_variable(ident, value),
                None => Err(ExecError::VariableNotFound(
                    name.to_string(),
                    ident.line_num,
                )),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::lang::token::TokenType;

    #[test]
    fn state() {
        let mut env = Environment::root();
        env.define_variable("a", Variable::Number(1.0));
        assert_eq!(
            env.access_variable(&Token::new(TokenType::Identifier, "a", 1))
                .unwrap(),
            Variable::Number(1.0)
        );

        assert_eq!(
            env.access_variable(&Token::new(TokenType::Identifier, "b", 1))
                .unwrap_err(),
            ExecError::VariableNotFound("b".to_string(), 1)
        );

        env.modify_variable(
            &Token::new(TokenType::Identifier, "a", 1),
            Variable::Number(2.0),
        )
        .unwrap();
        assert_eq!(
            env.access_variable(&Token::new(TokenType::Identifier, "a", 1))
                .unwrap(),
            Variable::Number(2.0)
        );
        assert_eq!(
            env.access_variable(&Token::new(TokenType::Identifier, "b", 1))
                .unwrap_err(),
            ExecError::VariableNotFound("b".to_string(), 1)
        );

        let mut env2 = Environment::derive(&Rc::new(RefCell::new(env)));
        env2.define_variable("b", Variable::Number(3.0));
        assert_eq!(
            env2.access_variable(&Token::new(TokenType::Identifier, "a", 1))
                .unwrap(),
            Variable::Number(2.0)
        );
        assert_eq!(
            env2.access_variable(&Token::new(TokenType::Identifier, "b", 1))
                .unwrap(),
            Variable::Number(3.0)
        );

        let mut env3 = Environment::derive(&Rc::new(RefCell::new(env2)));

        assert_eq!(
            env3.access_variable(&Token::new(TokenType::Identifier, "a", 1))
                .unwrap(),
            Variable::Number(2.0)
        );
        assert_eq!(
            env3.access_variable(&Token::new(TokenType::Identifier, "b", 1))
                .unwrap(),
            Variable::Number(3.0)
        );

        env3.modify_variable(
            &Token::new(TokenType::Identifier, "a", 1),
            Variable::Number(4.0),
        )
        .unwrap();
        assert_eq!(
            env3.access_variable(&Token::new(TokenType::Identifier, "a", 1))
                .unwrap(),
            Variable::Number(4.0)
        );
    }
}

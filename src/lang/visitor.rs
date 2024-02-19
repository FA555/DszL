use crate::{
    api::interact::Interact,
    lang::{
        environment::Environment,
        expr::{Expr, ExprVisitor},
        result::{ExecError, ExecResult},
        statement::{Statement, StatementVisitor, TimeoutAction},
        token::TokenType,
        variable::{Function, Variable},
    },
};
use std::{cell::RefCell, rc::Rc, sync::Arc};

/// `Visitor` struct encapsulates the functionality for visiting and processing expressions and statements. It is
/// designed to work with an environment for variable storage and manipulation, along with an interaction interface for
/// input and output operations.
///
/// This struct is central to the interpretation of the language, providing the logic to execute the various language
/// constructs.
pub(crate) struct Visitor {
    /// Local environment for variable storage and retrieval during the execution.
    env: Rc<RefCell<Environment>>,
    /// Interactor for handling input and output operations.
    interactor: Arc<dyn Interact>,
}

impl Visitor {
    /// Logs a message for debugging purposes.
    ///
    /// # Arguments
    ///
    /// - `msg`: The message to be logged.
    fn log(&self, msg: &str) {
        debug!("{}: {}", "Visitor", msg);
    }

    /// Creates a new `Visitor` instance with a given interactor for input and output.
    ///
    /// # Arguments
    ///
    /// - `interactor`: An `Arc` pointing to an object implementing the `Interact` trait.
    ///
    /// # Returns
    ///
    /// - `Visitor`: A new instance of `Visitor`.
    pub(crate) fn with_interactor(interactor: Arc<dyn Interact>) -> Self {
        Visitor {
            env: Rc::new(RefCell::new(Environment::root())),
            interactor,
        }
    }

    /// Evaluates an expression and returns the resulting variable.
    ///
    /// # Arguments
    ///
    /// - `expr`: A reference to the expression to evaluate.
    ///
    /// # Returns
    ///
    /// - `ExecResult<Variable>`: The result of the expression evaluation.
    fn evaluate(&mut self, expr: &Expr) -> ExecResult<Variable> {
        expr.dispatch_visit(self)
    }

    /// Executes a single statement.
    ///
    /// # Arguments
    ///
    /// - `statement`: A reference to the statement to execute.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of the statement execution.
    pub(crate) fn execute(&mut self, statement: &Statement) -> ExecResult<()> {
        statement.dispatch_visit(self).map(|_| ())
    }

    /// Executes a sequence of statements.
    ///
    /// # Arguments
    ///
    /// - `statements`: A vector of statements to execute.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of executing the sequence of statements.
    pub(crate) fn executes(&mut self, statements: Vec<Statement>) -> ExecResult<()> {
        for statement in statements {
            self.execute(&statement)?;
        }
        Ok(())
    }

    /// Executes a sequence of statements within a given environment.
    ///
    /// # Arguments
    ///
    /// - `statements`: A slice of statements to execute.
    /// - `env`: The environment in which to execute the statements.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of executing the statements within the environment.
    pub(crate) fn executes_with_env(
        &mut self,
        statements: &[Statement],
        env: Rc<RefCell<Environment>>,
    ) -> ExecResult<()> {
        let old_env = self.env.clone();
        self.env = env;
        let res = self.executes(statements.to_vec());
        self.env = old_env;
        res
    }
}

impl ExprVisitor<Variable> for Visitor {
    /// Visits an assign expression, evaluates its right-hand side, and assigns the result to a variable in the
    /// environment.
    ///
    /// # Arguments
    ///
    /// - `expr`: The expression to visit, expected to be an `Expr::Assign` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<Variable>`: The result of the assignment operation.
    fn visit_assign(&mut self, expr: &Expr) -> ExecResult<Variable> {
        if let Expr::Assign { lhs, rhs } = expr {
            self.log(&format!("assign {} <- {}", lhs, rhs));

            let value = self.evaluate(rhs)?;
            self.env.borrow_mut().modify_variable(lhs, value.clone())?;
            self.log(&format!("assigned {} to {}", value, lhs));
            Ok(value)
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a binary expression, evaluates its operands, and performs the specified binary operation.
    ///
    /// # Arguments
    ///
    /// - `expr`: The expression to visit, expected to be an `Expr::Binary` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<Variable>`: The result of the binary operation.
    fn visit_binary(&mut self, expr: &Expr) -> ExecResult<Variable> {
        if let Expr::Binary { lhs, op, rhs } = expr {
            self.log(&format!("binary {} {} {}", lhs, op, rhs));

            let lhs = self.evaluate(lhs)?;
            let rhs = self.evaluate(rhs)?;
            let map_wrapper =
                |res: Option<Variable>| res.ok_or(ExecError::IncompatibleOperandTypes(op.line_num));
            match op.typ {
                TokenType::Plus => map_wrapper(Variable::add(&lhs, &rhs)),
                TokenType::Minus => map_wrapper(Variable::sub(&lhs, &rhs)),
                TokenType::LAnd => map_wrapper(Variable::land(&lhs, &rhs)),
                TokenType::LOr => map_wrapper(Variable::lor(&lhs, &rhs)),
                TokenType::Equal => map_wrapper(Variable::eq(&lhs, &rhs)),
                TokenType::NotEqual => map_wrapper(Variable::ne(&lhs, &rhs)),
                TokenType::Less => map_wrapper(Variable::lt(&lhs, &rhs)),
                TokenType::LessEqual => map_wrapper(Variable::le(&lhs, &rhs)),
                TokenType::Greater => map_wrapper(Variable::gt(&lhs, &rhs)),
                TokenType::GreaterEqual => map_wrapper(Variable::ge(&lhs, &rhs)),
                TokenType::Match => map_wrapper(Variable::match_(&lhs, &rhs)),
                _ => Err(ExecError::Unreachable),
            }
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a function call expression, evaluates the function and arguments, and executes the function if callable.
    ///
    /// # Arguments
    ///
    /// - `expr`: The expression to visit, expected to be an `Expr::Call` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<Variable>`: The result of the function call.
    fn visit_call(&mut self, expr: &Expr) -> ExecResult<Variable> {
        if let Expr::Call { func, args } = expr {
            self.log(&format!("call {} with {:?}", func, args));

            if let Variable::Callable(func) = self.evaluate(func)? {
                // check if callable
                let args: Vec<_> = args
                    .iter()
                    .map(|expr| self.evaluate(expr))
                    .filter_map(Result::ok)
                    .collect();
                if args.len() == func.accept_param_amount() {
                    // check if correct number of arguments
                    func.call(self, &args)
                } else {
                    Err(ExecError::IncorrectParameterAmount(
                        func.accept_param_amount(),
                        args.len(),
                    ))
                }
            } else {
                Err(ExecError::CallOnNonCallable)
            }
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a literal expression and returns the corresponding variable.
    ///
    /// # Arguments
    ///
    /// - `expr`: The expression to visit, expected to be an `Expr::Literal` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<Variable>`: The variable corresponding to the literal.
    fn visit_literal(&mut self, expr: &Expr) -> ExecResult<Variable> {
        if let Expr::Literal(v) = expr {
            self.log(&format!("literal {}", v));

            Ok(Variable::from_value(v.clone()))
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a unary expression, evaluates its operand, and performs the specified unary operation.
    ///
    /// # Arguments
    ///
    /// - `expr`: The expression to visit, expected to be an `Expr::Unary` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<Variable>`: The result of the unary operation.
    fn visit_unary(&mut self, expr: &Expr) -> ExecResult<Variable> {
        if let Expr::Unary { op, rhs } = expr {
            self.log(&format!("unary {} {}", op, rhs));

            let rhs = self.evaluate(rhs)?;
            match op.typ {
                TokenType::Plus => Ok(rhs),
                TokenType::Minus => rhs
                    .neg()
                    .ok_or(ExecError::IncompatibleOperandTypes(op.line_num)),
                TokenType::Bang => rhs
                    .not()
                    .ok_or(ExecError::IncompatibleOperandTypes(op.line_num)),
                _ => Err(ExecError::Unreachable),
            }
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a variable expression and retrieves its value from the environment.
    ///
    /// # Arguments
    ///
    /// - `expr`: The expression to visit, expected to be an `Expr::Variable` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<Variable>`: The value of the variable from the environment.
    fn visit_variable(&mut self, expr: &Expr) -> ExecResult<Variable> {
        if let Expr::Variable(v) = expr {
            self.log(&format!("access variable {}", v));
            match self.env.borrow().access_variable(v) {
                Ok(val) => {
                    self.log(&format!("accessed variable {} with value `{}`", v, val));
                    Ok(val)
                }
                Err(e) => Err(e),
            }
        } else {
            Err(ExecError::Unreachable)
        }
    }
}

impl StatementVisitor<()> for Visitor {
    /// Visits a block statement and executes each statement within a new derived environment.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::Block` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of executing the block statement.
    fn visit_block(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::Block(statements) = statement {
            self.log(&format!("block {:?}", statements));

            let env = Rc::new(RefCell::new(Environment::derive(&self.env)));
            // execute the statements within the derived environment
            self.executes_with_env(statements, env)?;
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits an exit statement and triggers the exit operation.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::Exit` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: Result of the exit operation.
    fn visit_exit(&mut self, statement: &Statement) -> ExecResult<()> {
        if matches!(statement, Statement::Exit) {
            self.log("exit");

            Err(ExecError::Exit) // trigger exit
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits an expression statement, evaluates the expression for its side effects.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::Expression` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of evaluating the expression.
    fn visit_expression(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::Expression(expr) = statement {
            self.log(&format!("expression {}", expr));

            self.evaluate(expr)?;
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a function (state) declaration, creating a function object and storing it in the environment.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::State` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of processing the function declaration.
    fn visit_function(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::State {
            ident,
            params,
            body,
        } = statement
        {
            self.log(&format!(
                "function {}({:?}) {{ {:?} }}",
                ident, params, body
            ));

            let func = Function::with_params(
                ident.clone(),
                params.clone(),
                body.clone(),
                self.env.clone(),
            );
            self.env
                .borrow_mut()
                .define_variable(&ident.lexeme, Variable::Callable(func));
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits an if statement, evaluates the condition, and executes the corresponding branch.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::If` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of executing the if statement.
    fn visit_if(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        {
            self.log(&format!(
                "if ({}) {} else {:?}",
                condition, then_branch, else_branch
            ));

            // evaluate condition
            let condition = self.evaluate(condition)?;
            if condition.is_truthy() {
                // fall in then branch
                self.execute(then_branch)?;
            } else if let Some(else_branch) = else_branch {
                // fall in else branch
                self.execute(else_branch)?;
            }
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits an input statement, retrieves input from the user, and stores it in the specified variable.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::Input` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of processing the input statement.
    fn visit_input(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::Input {
            ident,
            timeout_action,
        } = statement
        {
            self.log(&format!("input {}", ident));

            if let Some(TimeoutAction { duration, action }) = timeout_action {
                // invoke input with timeout
                let duration = match self.evaluate(duration)? {
                    Variable::Number(n) => std::time::Duration::from_secs_f64(n),
                    _ => return Err(ExecError::IncompatibleType),
                };

                match self.interactor.input_timeout(duration) {
                    Some(s) => {
                        // timeout didn't occur
                        self.env
                            .borrow_mut()
                            .modify_variable(ident, Variable::Str(s.trim_end().to_string()))?;
                    }
                    None => {
                        // timeout occurred, a miserable one.
                        self.execute(action)?;
                    }
                }
            } else {
                // no timeout with input
                let s = self.interactor.input();
                self.env
                    .borrow_mut()
                    .modify_variable(ident, Variable::Str(s.trim_end().to_string()))?;
            }
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits an input_num statement, retrieves a numeric input from the user, and stores it in the specified variable.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::InputNum` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of processing the input_num statement.
    fn visit_input_num(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::InputNum {
            ident,
            timeout_action,
        } = statement
        {
            self.log(&format!("input_num {}", ident));

            if let Some(TimeoutAction { duration, action }) = timeout_action {
                // invoke input with timeout
                let duration = match self.evaluate(duration)? {
                    Variable::Number(n) => std::time::Duration::from_secs_f64(n),
                    _ => return Err(ExecError::IncompatibleType),
                };
                loop {
                    // loop until valid input
                    match self.interactor.input_timeout(duration) {
                        Some(s) => {
                            let n = match s.trim_end().parse::<f64>() {
                                Ok(n) => n,
                                Err(_) => {
                                    self.interactor.output("输入不是数字，请重新输入。");
                                    continue;
                                }
                            };
                            self.env
                                .borrow_mut()
                                .modify_variable(ident, Variable::Number(n))?;
                            break;
                        }
                        None => {
                            self.execute(action)?;
                        }
                    }
                }
            } else {
                // no timeout with input
                loop {
                    // loop until valid input
                    let s = self.interactor.input();
                    let n = match s.trim_end().parse::<f64>() {
                        Ok(n) => n,
                        Err(_) => {
                            self.interactor.output("输入不是数字，请重新输入。");
                            continue;
                        }
                    };
                    self.env
                        .borrow_mut()
                        .modify_variable(ident, Variable::Number(n))?;
                    break;
                }
            }
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits an output statement, evaluates the expression, and sends the result to the output.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::Output` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of processing the output statement.
    fn visit_output(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::Output(expr) = statement {
            self.log(&format!("output {}", expr));

            let value = self.evaluate(expr)?;
            self.interactor.output(&value.to_string());
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a sleep statement, evaluates the expression, and pauses execution for the specified duration.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::Sleep` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of processing the sleep statement.
    fn visit_sleep(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::Sleep(expr) = statement {
            self.log(&format!("sleep {}", expr));

            let value = self.evaluate(expr)?;
            if let Variable::Number(n) = value {
                std::thread::sleep(std::time::Duration::from_secs_f64(n));
                Ok(())
            } else {
                Err(ExecError::IncompatibleType)
            }
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a let statement, evaluates the initialiser if present, and defines a variable in the environment.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::Let` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of processing the let statement.
    fn visit_let(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::Let { ident, initialiser } = statement {
            self.log(&format!("let {} = {:?}", ident, initialiser));

            let value = match initialiser {
                Some(expr) => self.evaluate(expr)?, // evaluate initialiser
                None => Variable::Nil, // default to nil
            };
            self.env
                .borrow_mut()
                .define_variable(&ident.lexeme, value.clone());
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }

    /// Visits a while statement, evaluates the condition, and repeatedly executes the body while the condition is true.
    ///
    /// # Arguments
    ///
    /// - `statement`: The statement to visit, expected to be a `Statement::While` variant.
    ///
    /// # Returns
    ///
    /// - `ExecResult<()>`: The result of processing the while statement.
    fn visit_while(&mut self, statement: &Statement) -> ExecResult<()> {
        if let Statement::While { condition, body } = statement {
            self.log(&format!("while ({}) {}", condition, body));

            while self.evaluate(condition)?.is_truthy() {
                self.execute(body)?;
            }
            Ok(())
        } else {
            Err(ExecError::Unreachable)
        }
    }
}

#[cfg(test)]
mod test {
    mod dummy {
        use crate::api::interact::Interact;
        use std::sync::{Arc, Mutex};

        pub(crate) struct DummyInteractorHelper {
            pub(crate) upcoming_input: Vec<Option<String>>,
            cur_pos: usize,
            pub(crate) output_stream: String,
        }

        impl DummyInteractorHelper {
            pub(crate) fn new() -> Self {
                Self {
                    upcoming_input: Vec::default(),
                    cur_pos: 0,
                    output_stream: String::default(),
                }
            }

            pub(crate) fn load_input(&mut self, s: &[Option<&str>]) {
                self.upcoming_input = s.iter().map(|s| s.map(|s| s.to_string())).collect();
                self.cur_pos = 0;
            }

            pub(crate) fn consume(&mut self) -> Option<String> {
                let s = self.upcoming_input.get(self.cur_pos).cloned().flatten();
                self.cur_pos += 1;
                s
            }

            pub(crate) fn output_push(&mut self, s: &str) {
                self.output_stream.push_str(s);
            }

            pub(crate) fn output_stream(&self) -> &str {
                &self.output_stream
            }
        }

        impl Default for DummyInteractorHelper {
            fn default() -> Self {
                Self::new()
            }
        }

        pub(crate) struct DummyInteractor {
            helper: Arc<Mutex<DummyInteractorHelper>>,
        }

        impl DummyInteractor {
            pub(crate) fn new() -> Self {
                Self {
                    helper: Arc::new(Mutex::new(DummyInteractorHelper::default())),
                }
            }

            pub(crate) fn load_input(&mut self, s: &[Option<&str>]) {
                let mut helper = self.helper.lock().unwrap();
                helper.load_input(s);
            }
        }

        impl Default for DummyInteractor {
            fn default() -> Self {
                Self::new()
            }
        }

        impl Interact for DummyInteractor {
            fn input(&self) -> String {
                let mut helper = self.helper.lock().unwrap();
                loop {
                    match helper.consume() {
                        Some(s) => return s,
                        None => {}
                    }
                }
            }

            fn input_timeout(&self, _duration: std::time::Duration) -> Option<String> {
                let mut helper = self.helper.lock().unwrap();
                helper.consume()
            }

            fn output(&self, s: &str) {
                let mut helper = self.helper.lock().unwrap();
                helper.output_push(s);
            }

            fn output_history(&self) -> String {
                let helper = self.helper.lock().unwrap();
                helper.output_stream().to_string()
            }
        }
    }

    use super::*;
    use crate::lang::{lexer::Lexer, parser::Parser};
    use dummy::DummyInteractor;

    #[test]
    fn while_output() {
        #[rustfmt::skip]
        let src =
r#"
let a = 1;
while (a < 10) {
    output a;
    a = a + 1;
}
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut visitor = Visitor::with_interactor(Arc::new(DummyInteractor::default()));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }

        assert_eq!(visitor.interactor.output_history(), "123456789");
    }

    #[test]
    fn branch() {
        #[rustfmt::skip]
        let src =
r#"
let a = 1;
branch (a <= 0) {
    output "not positive";
} else {
    output "a = " + a;
}
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut visitor = Visitor::with_interactor(Arc::new(DummyInteractor::default()));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }

        assert_eq!(visitor.interactor.output_history(), "a = 1");
    }

    #[test]
    fn function() {
        #[rustfmt::skip]
        let src =
r#"
state test(a b c d e f) {
    output a + b + c + d + e + f;
}

test(1 1 4 5 1 4);
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut visitor = Visitor::with_interactor(Arc::new(DummyInteractor::default()));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }

        assert_eq!(visitor.interactor.output_history(), "16");
    }

    #[test]
    fn input() {
        #[rustfmt::skip]
        let src =
r#"
let a = "";
input a;
output a;
let b = "";
input_num b;
output b;
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut interactor = DummyInteractor::default();
        interactor.load_input(&[Some("hello, fa_"), Some("555")]);
        let mut visitor = Visitor::with_interactor(Arc::new(interactor));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }

        assert_eq!(visitor.interactor.output_history(), "hello, fa_555");
    }

    #[test]
    fn input_timeout() {
        #[rustfmt::skip]
        let src =
r#"
let a = "";
input a timeout(5) {
    a = "timeout";
};

let b = 0;
input_num b timeout(5) {
    b = 114514;
};

output a + b;
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut interactor = DummyInteractor::default();
        interactor.load_input(&[None, Some("1919810")]);
        let mut visitor = Visitor::with_interactor(Arc::new(interactor));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }

        assert_eq!(visitor.interactor.output_history(), "timeout1919810");
    }

    #[test]
    #[should_panic]
    fn incompatible_operand_types() {
        #[rustfmt::skip]
        let src =
r#"
let a = 1;
let b = "1";
output a < b;
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut visitor = Visitor::with_interactor(Arc::new(DummyInteractor::default()));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }
    }

    #[test]
    #[should_panic]
    fn incorrect_parameter_amount() {
        #[rustfmt::skip]
        let src =
r#"
state test(a b c) {
    output a + b + c;
}

test(1 1 4 5);
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut visitor = Visitor::with_interactor(Arc::new(DummyInteractor::default()));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }
    }

    #[test]
    #[should_panic]
    fn variable_not_found() {
        #[rustfmt::skip]
        let src =
r#"
output a;
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());

        let (statements, errors) = Parser::with_tokens(tokens).parse_effective();
        assert!(errors.is_empty());

        let mut visitor = Visitor::with_interactor(Arc::new(DummyInteractor::default()));
        match visitor.executes(statements) {
            Ok(_) | Err(ExecError::Exit) => {}
            Err(e) => panic!("Execution failed with error: {}", e),
        }
    }
}

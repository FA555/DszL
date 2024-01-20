use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
pub(crate) enum LexError {
    #[error("Reached end of file.")]
    ReachedEof,
    #[error("Invalid token '{0}' at line {1}.")]
    InvalidToken(char, usize),
    #[error("Unterminated string at line {0}.")]
    UnterminatedString(usize),
    #[error("Unterminated comment at line {0}.")]
    UnterminatedComment(usize),
    #[error("Invalid number '{0}' at line {1}.")]
    InvalidNumber(String, usize),
    #[error("Invalid character '{0}' at line {1}.")]
    InvalidCharacter(char, usize),
}

// pub(crate) type LexResult<T> = std::result::Result<T, LexError>;

#[derive(Clone, Debug, Error, PartialEq)]
pub(crate) enum ParseError {
    #[error("Left parenthesis expected at line {0}.")]
    LeftParenExpected(usize),
    #[error("Right parenthesis expected at line {0}.")]
    RightParenExpected(usize),
    #[error("Left brace expected at line {0}.")]
    LeftBraceExpected(usize),
    #[error("Right brace expected at line {0}.")]
    RightBraceExpected(usize),
    #[error("Identifier expected at line {0}.")]
    IdentifierExpected(usize),
    #[error("Semicolon expected at line {0}.")]
    SemiColonExpected(usize),
    #[error("Unexpected token '{0}' at line {1}.")]
    UnexpectedToken(String, usize),
    #[error("Unexpected end of file.")]
    UnexpectedEof,
}

pub(crate) type ParseResult<T> = std::result::Result<T, ParseError>;

#[derive(Clone, Debug, Error, PartialEq)]
pub(crate) enum ExecError {
    #[error("Call on non-callable type.")]
    CallOnNonCallable,
    #[error("Incompatible operand types at line {0}.")]
    IncompatibleOperandTypes(usize),
    #[error("Incompatible type.")]
    IncompatibleType,
    #[error("Incorrect parameter amount. Expected {0}, got {1}.")]
    IncorrectParameterAmount(usize, usize),
    #[error("Unreachable!")]
    Unreachable,
    #[error("Variable '{0}' not found at line {1}.")]
    VariableNotFound(String, usize),
    #[error("Exit statement.")]
    Exit,
}

pub(crate) type ExecResult<T> = std::result::Result<T, ExecError>;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn lex_error() {
        use LexError::*;
        assert_eq!(ReachedEof, ReachedEof);
        assert_eq!(InvalidToken('a', 1), InvalidToken('a', 1));
        assert_eq!(UnterminatedString(1), UnterminatedString(1));
        assert_eq!(UnterminatedComment(1), UnterminatedComment(1));
        assert_eq!(
            InvalidNumber("1".to_string(), 1),
            InvalidNumber("1".to_string(), 1)
        );
        assert_eq!(InvalidCharacter('a', 1), InvalidCharacter('a', 1));
    }

    // #[test]
    // fn lex_result() {
    //     use LexError::*;
    //     let a: LexResult<i32> = Ok(1);
    //     assert_eq!(a, Ok(1));
    //     let b: LexResult<()> = Err(ReachedEof);
    //     assert_eq!(b, Err(ReachedEof));
    //     let c: LexResult<()> = Err(Unknown);
    //     assert_eq!(c, Err(Unknown));
    // }

    #[test]
    fn parse_error() {
        use ParseError::*;
        assert_eq!(LeftParenExpected(1), LeftParenExpected(1));
        assert_eq!(RightParenExpected(1), RightParenExpected(1));
        assert_eq!(LeftBraceExpected(1), LeftBraceExpected(1));
        assert_eq!(RightBraceExpected(1), RightBraceExpected(1));
        assert_eq!(IdentifierExpected(1), IdentifierExpected(1));
        assert_eq!(SemiColonExpected(1), SemiColonExpected(1));
        assert_eq!(
            UnexpectedToken("a".to_string(), 1),
            UnexpectedToken("a".to_string(), 1)
        );
        assert_eq!(UnexpectedEof, UnexpectedEof);
    }

    #[test]
    fn parse_result() {
        use ParseError::*;
        let a: ParseResult<i32> = Ok(1);
        assert_eq!(a, Ok(1));
        let b: ParseResult<()> = Err(LeftParenExpected(1));
        assert_eq!(b, Err(LeftParenExpected(1)));
    }

    #[test]
    fn exec_error() {
        use ExecError::*;
        assert_eq!(CallOnNonCallable, CallOnNonCallable);
        assert_eq!(IncompatibleOperandTypes(1), IncompatibleOperandTypes(1));
        assert_eq!(IncompatibleType, IncompatibleType);
        assert_eq!(
            IncorrectParameterAmount(1, 2),
            IncorrectParameterAmount(1, 2)
        );
        assert_eq!(Unreachable, Unreachable);
        assert_eq!(
            VariableNotFound("a".to_string(), 1),
            VariableNotFound("a".to_string(), 1)
        );
        assert_eq!(Exit, Exit);
    }

    #[test]
    fn exec_result() {
        use ExecError::*;
        let a: ExecResult<i32> = Ok(1);
        assert_eq!(a, Ok(1));
        let b: ExecResult<()> = Err(CallOnNonCallable);
        assert_eq!(b, Err(CallOnNonCallable));
    }
}

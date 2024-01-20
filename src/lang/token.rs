use crate::lang::result::LexError;
use lazy_static::lazy_static;

/// `TokenType` represents the different types of tokens that can be encountered in the parsing
/// process of a programming language or script. These tokens are the basic building blocks for the
/// syntactic analysis, acting as the smallest units of meaning in the language's grammar.
///
/// The enum covers a wide range of token types including:
///
/// - Single-character tokens, which are often used for punctuation or simple operators. Examples
///   include semicolons (`;`), parentheses (`(`, `)`), and braces (`{`, `}`).
///
/// - Operators, which are symbols that represent various operations like arithmetic (`+`, `-`),
///   logical negation (`!`), assignment (`=`), equality comparison (`==`), and inequality
///   comparison (`!=`).
///
/// - Literals, which represent fixed values in the code. This includes identifiers (variable names,
///   function names etc.), strings, and numeric values (floating-point numbers).
///
/// - Keywords, which are reserved words that have special meaning in the language. This includes
///   control flow keywords (`if`, `loop`, `state`), variable declaration (`let`), and others like
///   `exit`, `output`, `sleep`, `input`, `inputNum`.
///
/// - Boolean and Nil values, represented by `True`, `False`, and `Nil`, for logical operations and
///   representing the absence of a value.
///
/// - `Eof` to signify the end of the input stream, a critical token for understanding when parsing
///   should cease.
///
/// This enum is derived from `Debug`, `Clone`, and `PartialEq` to allow for easy logging, cloning,
/// and comparison operations, which are essential for efficient parsing and interpretation of
/// tokens.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum TokenType {
    // Single-character tokens
    SemiColon,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,

    // Operators
    Plus,
    Minus,
    LAnd,
    LOr,
    Assign,
    Match,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Bang,

    // Literals
    Identifier,
    /// `String` represents a string literal, which is a sequence of characters
    Str(String),
    /// `Number` represents a numeric literal, which is a floating-point value
    Number(f64),

    // Keywords
    If,
    Else,
    While,
    State,
    Let,
    Input,
    InputNum,
    Timeout,
    Output,
    Exit,
    Sleep,

    Nil,
    True,
    False,

    // Comments and Whitespace
    InlineComment,
    BlockComment,
    Whitespace,
    Eof,
    Error(LexError),
}

lazy_static! {
    /// `KEYWORDS` is a `HashMap` that maps keywords to their corresponding `TokenType` values. This
    /// is used to quickly determine whether a given identifier is a keyword or not, and if so,
    /// which keyword it is.
    ///
    /// This is a `lazy_static` variable, which means that it is initialized lazily, i.e. the first
    /// time it is used. This is done to avoid unnecessary initialization of the `HashMap` when it
    /// is not needed.
    pub(crate) static ref KEYWORDS: std::collections::HashMap<String, TokenType> = {
        [
            ("branch".to_string(), TokenType::If),
            ("else".to_string(), TokenType::Else),
            ("while".to_string(), TokenType::While),
            ("state".to_string(), TokenType::State),
            ("let".to_string(), TokenType::Let),
            ("exit".to_string(), TokenType::Exit),
            ("output".to_string(), TokenType::Output),
            ("sleep".to_string(), TokenType::Sleep),
            ("input".to_string(), TokenType::Input),
            ("input_num".to_string(), TokenType::InputNum),
            ("timeout".to_string(), TokenType::Timeout),
            ("nil".to_string(), TokenType::Nil),
            ("true".to_string(), TokenType::True),
            ("false".to_string(), TokenType::False),

            ("分支".to_string(), TokenType::If),
            ("否则".to_string(), TokenType::Else),
            ("循环".to_string(), TokenType::While),
            ("状态".to_string(), TokenType::State),
            ("定义".to_string(), TokenType::Let),
            ("退出".to_string(), TokenType::Exit),
            ("输出".to_string(), TokenType::Output),
            ("等待".to_string(), TokenType::Sleep),
            ("输入".to_string(), TokenType::Input),
            ("输入数字".to_string(), TokenType::InputNum),
            ("超时".to_string(), TokenType::Timeout),
            ("空".to_string(), TokenType::Nil),
            ("真".to_string(), TokenType::True),
            ("假".to_string(), TokenType::False),
        ].into_iter().collect()
    };
}

/// A single token in the parsing process of a programming language or script. Each token is a unit
/// of meaning in the language's grammar, encapsulating a specific type (`TokenType`), the actual
/// text (lexeme) that it represents, and its location within the source (line number).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Token {
    /// The type of the token, represented by the `TokenType` enum.
    pub(crate) typ: TokenType,
    /// A `String` containing the actual text that this token represents.
    pub(crate) lexeme: String,
    /// The line number in the source code where this token was found.
    pub(crate) line_num: usize,
}

impl Token {
    /// ## `new`
    /// Constructs a new `Token`. This method provides a convenient way to create a new token with
    /// the given type, lexeme, and line number.
    ///
    /// ### Arguments
    ///
    /// - `typ`: The `TokenType` of the new token.
    /// - `lexeme`: A slice of the source code representing the text of the token.
    /// - `line`: The line number where the token is located.
    ///
    /// ### Returns
    ///
    /// Returns a new instance of `Token`.
    pub(crate) fn new(typ: TokenType, lexeme: &str, line: usize) -> Self {
        Token {
            typ,
            lexeme: String::from(lexeme),
            line_num: line,
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.typ {
            TokenType::Str(s) => write!(f, "String {}: {}", self.lexeme, s),
            TokenType::Number(n) => write!(f, "Number {}: {}", self.lexeme, n),
            _ => write!(f, "{:?} {}", self.typ, self.lexeme),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn creation() {
        let token = Token::new(TokenType::SemiColon, ";", 114);
        assert_eq!(token.typ, TokenType::SemiColon);
        assert_eq!(token.lexeme, ";");
        assert_eq!(token.line_num, 114);

        let token = Token::new(TokenType::Number(1.0), "1", 514);
        assert_eq!(token.typ, TokenType::Number(1.0));
        assert_eq!(token.lexeme, "1");
        assert_eq!(token.line_num, 514);
    }

    #[test]
    fn display() {
        let token = Token::new(TokenType::SemiColon, ";", 1);
        assert_eq!(format!("{}", token), "SemiColon ;");

        let token = Token::new(TokenType::Number(1.0), "1", 1);
        assert_eq!(format!("{}", token), "Number 1: 1");

        let token = Token::new(TokenType::Str(String::from("Hello")), "\"Hello\"", 1);
        assert_eq!(format!("{}", token), "String \"Hello\": Hello");
    }

    #[test]
    fn keyword_map() {
        assert_eq!(KEYWORDS.get("branch"), Some(&TokenType::If));
        assert_eq!(KEYWORDS.get("else"), Some(&TokenType::Else));
        assert_eq!(KEYWORDS.get("while"), Some(&TokenType::While));
        assert_eq!(KEYWORDS.get("let"), Some(&TokenType::Let));
        assert_eq!(KEYWORDS.get("exit"), Some(&TokenType::Exit));
        assert_eq!(KEYWORDS.get("output"), Some(&TokenType::Output));
        assert_eq!(KEYWORDS.get("sleep"), Some(&TokenType::Sleep));
        assert_eq!(KEYWORDS.get("input"), Some(&TokenType::Input));
        assert_eq!(KEYWORDS.get("input_num"), Some(&TokenType::InputNum));
        assert_eq!(KEYWORDS.get("timeout"), Some(&TokenType::Timeout));
        assert_eq!(KEYWORDS.get("nil"), Some(&TokenType::Nil));
        assert_eq!(KEYWORDS.get("true"), Some(&TokenType::True));
        assert_eq!(KEYWORDS.get("false"), Some(&TokenType::False));
    }
}

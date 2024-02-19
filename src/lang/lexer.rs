use crate::lang::{
    result::LexError,
    token::{Token, TokenType, KEYWORDS},
};

/// The `Lexer` is responsible for breaking down the source code into a series of tokens. This
/// process, known as lexical analysis or tokenization, is fundamental in the parsing process of a
/// programming language or script. The lexer reads the source code and converts it into a stream of
/// `Token` instances, each representing a meaningful unit in the language's grammar.
#[derive(Debug)]
pub(crate) struct Lexer {
    /// A vector of characters representing the source code to be tokenized.
    src: Vec<char>,
    // tokens: Vec<Token>,
    /// The starting position of the current token in `src`.
    start_pos: usize,
    /// The current position in `src` during scanning.
    cur_pos: usize,
    /// The current line number in the source code, used for error reporting.
    line_num: usize,
}

impl Lexer {
    /// Creates a new `Lexer` instance for lexical analysis.
    ///
    /// # Arguments
    ///
    /// - `src`: A `&str` reference to the source code that needs to be tokenized.
    ///
    /// # Returns
    ///
    /// A `Lexer` instance initialized with the provided source code.
    pub(crate) fn with_source(src: &str) -> Self {
        let mut src: Vec<_> = src.chars().collect();

        // Add a newline at the end of the source code if it doesn't already exist.
        if src.last() != Some(&'\n') {
            src.push('\n');
        }

        Lexer {
            src,
            // tokens: Vec::default(),
            start_pos: 0,
            cur_pos: 0,
            line_num: 1,
        }
    }

    /// Checks if the lexer has reached the end of the source code.
    ///
    /// # Returns
    ///
    /// `true` if the end of the source code is reached, `false` otherwise.
    #[allow(unused)]
    fn reached_end(&self) -> bool {
        self.cur_pos >= self.src.len()
    }

    /// Peeks at the current character in the source code without advancing the cursor.
    ///
    /// # Returns
    ///
    /// An `Option<char>` containing the current character if available, or `None` if the end is
    /// reached.
    fn peek(&self) -> Option<char> {
        self.src.get(self.cur_pos).copied()
    }

    /// Peeks at a character in the source code at a specified offset from the current position
    /// without advancing the cursor.
    ///
    /// # Arguments
    ///
    /// - `offset`: The number of characters to offset from the current position.
    ///
    /// # Returns
    ///
    /// An `Option<char>` containing the character at the offset position, or `None` if out of
    /// bounds.
    #[allow(unused)]
    fn peek_offset(&self, offset: usize) -> Option<char> {
        self.src.get(self.cur_pos + offset).copied()
    }

    /// Advances the cursor in the source code by one character and returns the character.
    ///
    /// # Returns
    ///
    /// An `Option<char>` containing the character at the current position before advancing, or
    /// `None` if the end is reached.
    fn advance(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.cur_pos += 1;
        Some(c)
    }
    /// Checks the next character and advances the cursor if it matches the specified character.
    ///
    /// # Arguments
    ///
    /// - `c`: The character to match against the next character in the source.
    ///
    /// # Returns
    ///
    /// `true` if the next character matches and the cursor is advanced, `false` otherwise.
    fn try_match(&mut self, c: char) -> bool {
        if self.peek() == Some(c) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Extracts the next token from the source code.
    ///
    /// # Returns
    ///
    /// A `Token` instance representing the next token in the source code. If an error occurs during
    /// tokenization, the token will have the `TokenType::Error` variant.
    pub(crate) fn next_token(&mut self) -> Token {
        self.start_pos = self.cur_pos;
        if self.peek().is_none() {
            return Token::new(TokenType::Eof, "", self.line_num);
        }

        let typ = match self.advance().unwrap() {
            '(' => TokenType::LeftParen,
            ')' => TokenType::RightParen,
            '{' => TokenType::LeftBrace,
            '}' => TokenType::RightBrace,
            '-' => TokenType::Minus,
            '+' => TokenType::Plus,
            ';' => TokenType::SemiColon,
            '!' => {
                if self.try_match('=') {
                    TokenType::NotEqual // !=
                } else {
                    TokenType::Bang
                }
            }
            '=' => {
                if self.try_match('=') {
                    TokenType::Equal // ==
                } else {
                    TokenType::Assign
                }
            }
            '/' => {
                if self.try_match('/') {
                    self.match_inline_comment() // //
                } else if self.try_match('*') {
                    self.match_block_comment() // /*
                } else {
                    TokenType::Error(LexError::InvalidToken('/', self.line_num))
                }
            }
            '<' => {
                if self.try_match('=') {
                    TokenType::LessEqual // <=
                } else {
                    TokenType::Less
                }
            }
            '>' => {
                if self.try_match('=') {
                    TokenType::GreaterEqual // >=
                } else {
                    TokenType::Greater
                }
            }
            '&' => {
                if self.try_match('&') {
                    TokenType::LAnd // &&
                } else {
                    TokenType::Error(LexError::InvalidToken('&', self.line_num))
                }
            }
            '|' => {
                if self.try_match('|') {
                    TokenType::LOr // ||
                } else {
                    TokenType::Error(LexError::InvalidToken('|', self.line_num))
                }
            }
            '~' => {
                if self.try_match('=') {
                    TokenType::Match // ~=
                } else {
                    TokenType::Error(LexError::InvalidToken('~', self.line_num))
                }
            }
            c if c.is_whitespace() => self.match_whitespace(c),
            '"' => self.match_string(),
            c if c.is_ascii_digit() || c == '.' => self.match_number(c),
            c if c.is_alphabetic() || c == '_' || !c.is_ascii() => self.match_identifier(c), // ident and keyword
            c => {
                return Token::new(
                    TokenType::Error(LexError::InvalidCharacter(c, self.line_num)),
                    &c.to_string(),
                    self.line_num,
                );
            }
        };

        if let TokenType::Error(LexError::InvalidToken(_, line_num)) = typ {
            return Token::new(typ, "", line_num);
        }

        self.cur_token(typ)
    }

    /// Creates a new token based on the current state of the lexer.
    ///
    /// # Arguments
    ///
    /// - `typ`: The `TokenType` of the new token.
    ///
    /// # Returns
    ///
    /// A `Token` instance representing the current state of the lexer. The token's lexeme is the
    /// slice of the source code from `start_pos` to `cur_pos`. The line number is set to the
    /// current line number.
    fn cur_token(&self, typ: TokenType) -> Token {
        match self.src.get(self.start_pos..self.cur_pos) {
            Some(s) => Token::new(typ, &s.iter().collect::<String>(), self.line_num),
            None => Token::new(TokenType::Error(LexError::ReachedEof), "", self.line_num),
        }
    }

    /// Parses an inline comment, advancing the cursor to the end of the comment.
    ///
    /// Inline comments start with `//` and continue until the end of the line.
    ///
    /// # Returns
    ///
    /// A `TokenType` representing the type of the inline comment.
    fn match_inline_comment(&mut self) -> TokenType {
        while let Some(c) = self.peek() {
            if c == '\n' {
                self.line_num += 1;
                break;
            }
            self.advance();
        }
        TokenType::InlineComment
    }

    /// Parses a block comment, handling nested comments and advancing the cursor to the end of the
    /// comment.
    ///
    /// Block comments start with `/*` and end with `*/`. This method handles nested block comments
    /// correctly.
    ///
    /// # Returns
    ///
    /// A `TokenType` representing the type of the block comment.
    fn match_block_comment(&mut self) -> TokenType {
        let mut depth = 1;
        while let Some(c) = self.advance() {
            if c == '\n' {
                self.line_num += 1;
            } else if c == '/' && self.try_match('*') {
                depth += 1; // nested comment level up
            } else if c == '*' && self.try_match('/') {
                depth -= 1; // nested comment level down
                if depth == 0 {
                    // reached the end of the outermost comment
                    break;
                }
            }
        }
        if depth != 0 {
            // unterminated comment
            return TokenType::Error(LexError::UnterminatedComment(self.line_num));
        }
        TokenType::BlockComment
    }

    /// Skips over whitespace characters in the source code and increments the line number on
    /// encountering new lines.
    ///
    /// # Arguments
    ///
    /// - `start`: The initial whitespace character that led to the invocation of this method.
    ///
    /// # Returns
    ///
    /// A `TokenType` representing the type of whitespace.
    fn match_whitespace(&mut self, start: char) -> TokenType {
        if start == '\n' {
            self.line_num += 1;
        }

        while let Some(c) = self.peek() {
            if !c.is_whitespace() {
                break;
            }
            self.advance();
            if c == '\n' {
                self.line_num += 1;
            } // note that there shouldn't be a break statement here
        }

        TokenType::Whitespace
    }

    /// Parses a string literal, handling escape sequences and advancing the cursor to the end of
    /// the string.
    ///
    /// String literals are enclosed in double quotes (`"`).
    ///
    /// # Returns
    ///
    /// A `TokenType` representing the type of the string literal. If an error occurs during parsing
    /// (e.g., unterminated string), the token will have the `TokenType::Error` variant.
    fn match_string(&mut self) -> TokenType {
        let mut s = String::default();
        while let Some(c) = self.advance() {
            if c == '"' {
                return TokenType::Str(s);
            } else if c == '\n' {
                self.line_num += 1;
                return TokenType::Error(LexError::UnterminatedString(self.line_num));
            } else {
                s.push(c);
            }
        }
        TokenType::Error(LexError::UnterminatedString(self.line_num))
    }

    /// Parses a number literal, handling different formats (e.g., integer, floating-point,
    /// scientific notation).
    ///
    /// # Arguments
    ///
    /// - `start`: The initial character that led to the invocation of this method, expected to be a
    /// digit.
    ///
    /// # Returns
    ///
    /// A `TokenType` representing the type of the number literal. If an error occurs during parsing
    /// (e.g., invalid number), the token will have the `TokenType::Error` variant.
    fn match_number(&mut self, start: char) -> TokenType {
        let mut s = String::default();
        s.push(start);

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() || c == '.' || c == '_' || c == 'e' || c == 'E' || c == '-' {
                // e for scientific notation valid in floating-point literals
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }

        match s.parse::<f64>() {
            Ok(n) => TokenType::Number(n),
            Err(_) => TokenType::Error(LexError::InvalidNumber(s, self.line_num)),
        }
    }

    /// Identifies an identifier or keyword from the source code and advances the cursor to the end
    /// of the identifier.
    ///
    /// This method differentiates between user-defined identifiers and reserved keywords.
    ///
    /// # Arguments
    ///
    /// - `start`: The initial character that led to the invocation of this method, expected to be
    /// alphabetic.
    ///
    /// # Returns
    ///
    /// A `TokenType` representing the type of the identifier. If the identifier is a reserved
    /// keyword, the corresponding `TokenType` will be returned. Otherwise, the token will have the
    /// `TokenType::Identifier` variant.
    fn match_identifier(&mut self, start: char) -> TokenType {
        let mut s = String::default();
        s.push(start);

        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' || !c.is_ascii() {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if let Some(typ) = KEYWORDS.get(&s) {
            // check if the identifier is a keyword
            typ.clone()
        } else {
            TokenType::Identifier
        }
    }

    /// Processes the entire source code and returns a vector of tokens.
    ///
    /// This method repeatedly calls `next_token` until the end of the source code is reached or an
    /// error occurs.
    ///
    /// # Returns
    ///
    /// A `Vec<Token>` containing all the tokens parsed from the source code. If an error occurs
    /// during tokenization, the token will have the `TokenType::Error` variant.
    pub(crate) fn lex(&mut self) -> Vec<Token> {
        let mut tokens = Vec::default();
        loop {
            match self.next_token() {
                Token {
                    typ: TokenType::Eof,
                    ..
                } => break,
                token => tokens.push(token),
            }
        }
        tokens
    }

    /// Processes the entire source code and returns a vector of tokens, excluding whitespace and
    /// comments.
    ///
    /// This method repeatedly calls `next_token` until the end of the source code is reached or an
    /// error occurs, and filters out whitespace and comments.
    ///
    /// # Returns
    ///
    /// A tuple containing two `Vec<Token>` instances. The first vector contains all the significant
    /// tokens parsed from the source code, and the second vector contains all the errors
    /// encountered during tokenization.
    pub(crate) fn lex_effective(&mut self) -> (Vec<Token>, Vec<Token>) {
        let tokens = self.lex();
        let mut significant_tokens = Vec::default();
        let mut errors = Vec::default();
        for token in tokens.into_iter() {
            match token.typ {
                TokenType::Whitespace
                | TokenType::InlineComment
                | TokenType::BlockComment
                | TokenType::Eof => {} // filter out whitespace and comments
                TokenType::Error(_) => errors.push(token),
                _ => significant_tokens.push(token),
            }
        }
        (significant_tokens, errors)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn creation() {
        let src = "let x = 1;\n";
        let lexer = Lexer::with_source(src);
        assert_eq!(lexer.src, src.chars().collect::<Vec<char>>());
        assert_eq!(lexer.start_pos, 0);
        assert_eq!(lexer.cur_pos, 0);
        assert_eq!(lexer.line_num, 1);
    }

    #[test]
    fn reached_end() {
        let src = "let x = 1;\n";
        let mut lexer = Lexer::with_source(src);
        assert!(!lexer.reached_end());
        lexer.cur_pos = src.len();
        assert!(lexer.reached_end());
    }

    #[test]
    fn peek() {
        let src = "let x = 1;\n";
        let mut lexer = Lexer::with_source(src);
        assert_eq!(lexer.peek(), Some('l'));
        lexer.cur_pos = 3;
        assert_eq!(lexer.peek(), Some(' '));
        lexer.cur_pos = 6;
        assert_eq!(lexer.peek(), Some('='));
        lexer.cur_pos = src.len();
        assert_eq!(lexer.peek(), None);
        lexer.cur_pos = 114514;
        assert_eq!(lexer.peek(), None);
    }

    #[test]
    fn peek_offset() {
        let src = "let x = 1;\n";
        let lexer = Lexer::with_source(src);
        assert_eq!(lexer.peek_offset(0), Some('l'));
        assert_eq!(lexer.peek_offset(3), Some(' '));
        assert_eq!(lexer.peek_offset(4), Some('x'));
        assert_eq!(lexer.peek_offset(6), Some('='));
        assert_eq!(lexer.peek_offset(8), Some('1'));
        assert_eq!(lexer.peek_offset(9), Some(';'));
        assert_eq!(lexer.peek_offset(10), Some('\n'));
        assert_eq!(lexer.peek_offset(11), None);
        assert_eq!(lexer.peek_offset(114514), None);
    }

    #[test]
    fn advance() {
        let src = "let x = 1;\n";
        let mut lexer = Lexer::with_source(src);
        assert_eq!(lexer.advance(), Some('l'));
        assert_eq!(lexer.cur_pos, 1);
        assert_eq!(lexer.advance(), Some('e'));
        assert_eq!(lexer.cur_pos, 2);
        lexer.cur_pos = src.len();
        assert_eq!(lexer.advance(), None);
        assert_eq!(lexer.cur_pos, src.len());
    }

    #[test]
    fn try_match() {
        let src = "let x = 1;\n";
        let mut lexer = Lexer::with_source(src);
        assert!(lexer.try_match('l'));
        assert_eq!(lexer.cur_pos, 1);
        assert!(lexer.try_match('e'));
        assert_eq!(lexer.cur_pos, 2);
        assert!(!lexer.try_match(' '));
        assert_eq!(lexer.cur_pos, 2);
        lexer.cur_pos = src.len();
        assert!(!lexer.try_match('t'));
        assert_eq!(lexer.cur_pos, src.len());
    }

    #[test]
    fn next_token() {
        let src = "let x = 1;\n";
        let mut lexer = Lexer::with_source(src);
        assert_eq!(lexer.next_token(), Token::new(TokenType::Let, "let", 1));
        assert_eq!(
            lexer.next_token(),
            Token::new(TokenType::Whitespace, " ", 1)
        );
        assert_eq!(
            lexer.next_token(),
            Token::new(TokenType::Identifier, "x", 1)
        );
        assert_eq!(
            lexer.next_token(),
            Token::new(TokenType::Whitespace, " ", 1)
        );
        assert_eq!(lexer.next_token(), Token::new(TokenType::Assign, "=", 1));
        assert_eq!(
            lexer.next_token(),
            Token::new(TokenType::Whitespace, " ", 1)
        );
        assert_eq!(
            lexer.next_token(),
            Token::new(TokenType::Number(1.0), "1", 1)
        );
        assert_eq!(lexer.next_token(), Token::new(TokenType::SemiColon, ";", 1));
        assert_eq!(
            lexer.next_token(),
            Token::new(TokenType::Whitespace, "\n", 2)
        );
        assert_eq!(lexer.next_token(), Token::new(TokenType::Eof, "", 2));
    }

    #[test]
    fn lex() {
        #[rustfmt::skip]
            let src =
            r#"state vegetable() {
    output "太菜了！";
    sleep 1;
}"#;
        let tokens = Lexer::with_source(src).lex();
        assert_eq!(tokens.len(), 20);
        assert_eq!(tokens[0], Token::new(TokenType::State, "state", 1));
        assert_eq!(tokens[1], Token::new(TokenType::Whitespace, " ", 1));
        assert_eq!(tokens[2], Token::new(TokenType::Identifier, "vegetable", 1));
        assert_eq!(tokens[3], Token::new(TokenType::LeftParen, "(", 1));
        assert_eq!(tokens[4], Token::new(TokenType::RightParen, ")", 1));
        assert_eq!(tokens[5], Token::new(TokenType::Whitespace, " ", 1));
        assert_eq!(tokens[6], Token::new(TokenType::LeftBrace, "{", 1));
        assert_eq!(tokens[7], Token::new(TokenType::Whitespace, "\n    ", 2));
        assert_eq!(tokens[8], Token::new(TokenType::Output, "output", 2));
        assert_eq!(tokens[9], Token::new(TokenType::Whitespace, " ", 2));
        assert_eq!(
            tokens[10],
            Token::new(TokenType::Str(String::from("太菜了！")), "\"太菜了！\"", 2)
        );
        assert_eq!(tokens[11], Token::new(TokenType::SemiColon, ";", 2));
        assert_eq!(tokens[12], Token::new(TokenType::Whitespace, "\n    ", 3));
        assert_eq!(tokens[13], Token::new(TokenType::Sleep, "sleep", 3));
        assert_eq!(tokens[14], Token::new(TokenType::Whitespace, " ", 3));
        assert_eq!(tokens[15], Token::new(TokenType::Number(1.0), "1", 3));
        assert_eq!(tokens[16], Token::new(TokenType::SemiColon, ";", 3));
        assert_eq!(tokens[17], Token::new(TokenType::Whitespace, "\n", 4));
        assert_eq!(tokens[18], Token::new(TokenType::RightBrace, "}", 4));
        assert_eq!(tokens[19], Token::new(TokenType::Whitespace, "\n", 5));
    }

    #[test]
    fn next_token_effective() {
        #[rustfmt::skip]
            let src =
            r#"state vegetable() {
    sleep 1;
    branch 114 == 514 {
        output "太菜了！";
    }
}
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 18);
        assert_eq!(tokens[0], Token::new(TokenType::State, "state", 1));
        assert_eq!(tokens[1], Token::new(TokenType::Identifier, "vegetable", 1));
        assert_eq!(tokens[2], Token::new(TokenType::LeftParen, "(", 1));
        assert_eq!(tokens[3], Token::new(TokenType::RightParen, ")", 1));
        assert_eq!(tokens[4], Token::new(TokenType::LeftBrace, "{", 1));
        assert_eq!(tokens[5], Token::new(TokenType::Sleep, "sleep", 2));
        assert_eq!(tokens[6], Token::new(TokenType::Number(1.0), "1", 2));
        assert_eq!(tokens[7], Token::new(TokenType::SemiColon, ";", 2));
        assert_eq!(tokens[8], Token::new(TokenType::If, "branch", 3));
        assert_eq!(tokens[9], Token::new(TokenType::Number(114.0), "114", 3));
        assert_eq!(tokens[10], Token::new(TokenType::Equal, "==", 3));
        assert_eq!(tokens[11], Token::new(TokenType::Number(514.0), "514", 3));
        assert_eq!(tokens[12], Token::new(TokenType::LeftBrace, "{", 3));
        assert_eq!(tokens[13], Token::new(TokenType::Output, "output", 4));
        assert_eq!(
            tokens[14],
            Token::new(TokenType::Str(String::from("太菜了！")), "\"太菜了！\"", 4)
        );
        assert_eq!(tokens[15], Token::new(TokenType::SemiColon, ";", 4));
        assert_eq!(tokens[16], Token::new(TokenType::RightBrace, "}", 5));
        assert_eq!(tokens[17], Token::new(TokenType::RightBrace, "}", 6));
    }

    #[test]
    fn efficient_chinese() {
        #[rustfmt::skip]
            let src =
            r#"状态 菜鸡() {
    等待 1;
    分支 114 != 514 {
        输出 "太菜了！";
    }
}
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 18);
        assert_eq!(tokens[0], Token::new(TokenType::State, "状态", 1));
        assert_eq!(tokens[1], Token::new(TokenType::Identifier, "菜鸡", 1));
        assert_eq!(tokens[2], Token::new(TokenType::LeftParen, "(", 1));
        assert_eq!(tokens[3], Token::new(TokenType::RightParen, ")", 1));
        assert_eq!(tokens[4], Token::new(TokenType::LeftBrace, "{", 1));
        assert_eq!(tokens[5], Token::new(TokenType::Sleep, "等待", 2));
        assert_eq!(tokens[6], Token::new(TokenType::Number(1.0), "1", 2));
        assert_eq!(tokens[7], Token::new(TokenType::SemiColon, ";", 2));
        assert_eq!(tokens[8], Token::new(TokenType::If, "分支", 3));
        assert_eq!(tokens[9], Token::new(TokenType::Number(114.0), "114", 3));
        assert_eq!(tokens[10], Token::new(TokenType::NotEqual, "!=", 3));
        assert_eq!(tokens[11], Token::new(TokenType::Number(514.0), "514", 3));
        assert_eq!(tokens[12], Token::new(TokenType::LeftBrace, "{", 3));
        assert_eq!(tokens[13], Token::new(TokenType::Output, "输出", 4));
        assert_eq!(
            tokens[14],
            Token::new(TokenType::Str(String::from("太菜了！")), "\"太菜了！\"", 4)
        );
        assert_eq!(tokens[15], Token::new(TokenType::SemiColon, ";", 4));
        assert_eq!(tokens[16], Token::new(TokenType::RightBrace, "}", 5));
        assert_eq!(tokens[17], Token::new(TokenType::RightBrace, "}", 6));
    }

    #[test]
    fn very_many_tokens() {
        let src = "let x = 1;\n".repeat(10000);
        let (tokens, errors) = Lexer::with_source(&src).lex_effective();
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 10000 * 5);
    }

    #[test]
    fn complicated_script() {
        #[rustfmt::skip]
            let src =
            r#"
let greeting = "Hello, world!";
output greeting;

input x;
let z = x - 3;
output z;

let a = 1.0e10;
let b = 1.0e-10;
let t = true;
let f = false;
let n = nil;
exit;
"#;

        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert!(errors.is_empty());
        assert_eq!(tokens.len(), 48);
        assert_eq!(tokens[0], Token::new(TokenType::Let, "let", 2));
        assert_eq!(tokens[1], Token::new(TokenType::Identifier, "greeting", 2));
        assert_eq!(tokens[2], Token::new(TokenType::Assign, "=", 2));
        assert_eq!(
            tokens[3],
            Token::new(
                TokenType::Str(String::from("Hello, world!")),
                "\"Hello, world!\"",
                2,
            )
        );
        assert_eq!(tokens[4], Token::new(TokenType::SemiColon, ";", 2));
        assert_eq!(tokens[5], Token::new(TokenType::Output, "output", 3));
        assert_eq!(tokens[6], Token::new(TokenType::Identifier, "greeting", 3));
        assert_eq!(tokens[7], Token::new(TokenType::SemiColon, ";", 3));
        assert_eq!(tokens[8], Token::new(TokenType::Input, "input", 5));
        assert_eq!(tokens[9], Token::new(TokenType::Identifier, "x", 5));
        assert_eq!(tokens[10], Token::new(TokenType::SemiColon, ";", 5));
        assert_eq!(tokens[11], Token::new(TokenType::Let, "let", 6));
        assert_eq!(tokens[12], Token::new(TokenType::Identifier, "z", 6));
        assert_eq!(tokens[13], Token::new(TokenType::Assign, "=", 6));
        assert_eq!(tokens[14], Token::new(TokenType::Identifier, "x", 6));
        assert_eq!(tokens[15], Token::new(TokenType::Minus, "-", 6));
        assert_eq!(tokens[16], Token::new(TokenType::Number(3.0), "3", 6));
        assert_eq!(tokens[17], Token::new(TokenType::SemiColon, ";", 6));
        assert_eq!(tokens[18], Token::new(TokenType::Output, "output", 7));
        assert_eq!(tokens[19], Token::new(TokenType::Identifier, "z", 7));
        assert_eq!(tokens[20], Token::new(TokenType::SemiColon, ";", 7));
        assert_eq!(tokens[21], Token::new(TokenType::Let, "let", 9));
        assert_eq!(tokens[22], Token::new(TokenType::Identifier, "a", 9));
        assert_eq!(tokens[23], Token::new(TokenType::Assign, "=", 9));
        assert_eq!(
            tokens[24],
            Token::new(TokenType::Number(1.0e10), "1.0e10", 9)
        );
        assert_eq!(tokens[25], Token::new(TokenType::SemiColon, ";", 9));
        assert_eq!(tokens[26], Token::new(TokenType::Let, "let", 10));
        assert_eq!(tokens[27], Token::new(TokenType::Identifier, "b", 10));
        assert_eq!(tokens[28], Token::new(TokenType::Assign, "=", 10));
        assert_eq!(
            tokens[29],
            Token::new(TokenType::Number(1.0e-10), "1.0e-10", 10)
        );
        assert_eq!(tokens[30], Token::new(TokenType::SemiColon, ";", 10));
        assert_eq!(tokens[31], Token::new(TokenType::Let, "let", 11));
        assert_eq!(tokens[32], Token::new(TokenType::Identifier, "t", 11));
        assert_eq!(tokens[33], Token::new(TokenType::Assign, "=", 11));
        assert_eq!(tokens[34], Token::new(TokenType::True, "true", 11));
        assert_eq!(tokens[35], Token::new(TokenType::SemiColon, ";", 11));
        assert_eq!(tokens[36], Token::new(TokenType::Let, "let", 12));
        assert_eq!(tokens[37], Token::new(TokenType::Identifier, "f", 12));
        assert_eq!(tokens[38], Token::new(TokenType::Assign, "=", 12));
        assert_eq!(tokens[39], Token::new(TokenType::False, "false", 12));
        assert_eq!(tokens[40], Token::new(TokenType::SemiColon, ";", 12));
        assert_eq!(tokens[41], Token::new(TokenType::Let, "let", 13));
        assert_eq!(tokens[42], Token::new(TokenType::Identifier, "n", 13));
        assert_eq!(tokens[43], Token::new(TokenType::Assign, "=", 13));
        assert_eq!(tokens[44], Token::new(TokenType::Nil, "nil", 13));
        assert_eq!(tokens[45], Token::new(TokenType::SemiColon, ";", 13));
        assert_eq!(tokens[46], Token::new(TokenType::Exit, "exit", 14));
        assert_eq!(tokens[47], Token::new(TokenType::SemiColon, ";", 14));
    }

    #[test]
    fn lex_error() {
        #[rustfmt::skip]
            let src =
            r#"
, :
x = 1e2e3;
y = "unterminated string;
z = 1.0e;
/* unterminated block comment
"#;
        let (tokens, errors) = Lexer::with_source(src).lex_effective();
        assert_eq!(tokens.len(), 8);
        assert_eq!(errors.len(), 6);
        assert_eq!(
            errors[0],
            Token::new(TokenType::Error(LexError::InvalidCharacter(',', 2)), ",", 2)
        );
        assert_eq!(
            errors[1],
            Token::new(TokenType::Error(LexError::InvalidCharacter(':', 2)), ":", 2)
        );
        assert_eq!(
            errors[2],
            Token::new(
                TokenType::Error(LexError::InvalidNumber(String::from("1e2e3"), 3)),
                "1e2e3",
                3,
            )
        );
        assert_eq!(
            errors[3],
            Token::new(
                TokenType::Error(LexError::UnterminatedString(5)),
                "\"unterminated string;\n",
                5,
            )
        );
        assert_eq!(
            errors[4],
            Token::new(
                TokenType::Error(LexError::InvalidNumber(String::from("1.0e"), 5)),
                "1.0e",
                5,
            )
        );
        assert_eq!(
            errors[5],
            Token::new(
                TokenType::Error(LexError::UnterminatedComment(7)),
                "/* unterminated block comment\n",
                7,
            )
        );
    }
}

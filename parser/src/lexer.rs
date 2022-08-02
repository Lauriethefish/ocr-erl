//! Takes the characters from a file of OCR Exam Reference Language code and represents them as tokens.

use crate::{
    err::{SyntaxError, SyntaxErrorKind},
    file::FilePosition,
    tokens::Token,
    Lexer,
};
use phf::phf_map;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{assert_err, err::SyntaxErrorKind, file, tokens::Token};

    #[macro_export]
    macro_rules! file {
        ($contents:expr) => {
            $crate::file::File::from_string($contents.to_string())
        };
    }

    #[macro_export]
    macro_rules! assert_err {
        ($actual:expr, $kind:expr, $from:expr, $to:expr, $line:expr) => {{
            match $actual {
                Ok(_) => {
                    panic!("Expected Err of kind {} but got Ok", $kind)
                }
                Err(err) => {
                    let from_pos = crate::file::FilePosition::new($line, $from, err.tag().file());
                    let to_pos = crate::file::FilePosition::new($line, $to, err.tag().file());
                    let expected_err = SyntaxError::new(from_pos, to_pos, $kind);

                    if expected_err != err {
                        panic!("Expected error {} but got {}", expected_err, err)
                    }
                }
            }
        }};
    }

    macro_rules! lexer {
        ($contents:expr) => {
            $crate::lexer::FileLexer::new(file!($contents).beginning())
        };
    }

    #[test]
    fn should_return_identifier() {
        let mut lexer = lexer!("example_IDENT123");
        assert_eq!(
            Token::Identifier("example_IDENT123".to_string()),
            lexer.consume_token().unwrap()
        )
    }

    /// A character that is non-alphanumeric and is not `_` indicates the end of an identifier and the start of the next token.
    /// TODO: Should other characters be permitted within identifiers?
    #[test]
    fn should_stop_parsing_identifier_at_invalid_char() {
        let mut lexer = lexer!("still_123_valid+not_valid");
        assert_eq!(
            Token::Identifier("still_123_valid".to_string()),
            lexer.consume_token().unwrap()
        )
    }

    /// Identifiers must begin with a letter in ERL.
    #[test]
    fn should_not_begin_identifier_without_letter() {
        let mut lexer = lexer!("_invalid_identifier");
        match lexer.consume_token() {
            Ok(Token::Identifier(_)) => panic!("Should not have read identifier!"),
            _ => {}
        }
    }

    /// Make sure that every reserved identifier is identified correctly.
    #[test]
    fn should_find_reserved_identifier() {
        for (name, token) in &RESERVED_IDENTIFIER_INDEX {
            let mut lexer = lexer!(name);
            assert_eq!(token, &lexer.consume_token().unwrap())
        }
    }

    /// Make sure that every operator is identified correctly
    #[test]
    fn should_find_operator() {
        for (chars, token) in &OPERATOR_SEPARATOR_INDEX {
            let mut lexer = lexer!(chars);
            assert_eq!(token, &lexer.consume_token().unwrap())
        }
    }

    /// TODO: Should escape characters be supported in string literals?
    /// The specification does not list them but they could be very useful.
    #[test]
    fn should_read_string_literal() {
        let mut lexer = lexer!("\"Hello World\"");
        assert_eq!(
            Token::StringLiteral("Hello World".to_string()),
            lexer.consume_token().unwrap()
        );
    }

    /// String literals are not allowed to go over lines currently.
    /// TODO: This is not explicitly disallowed, so perhaps should be permitted by this lexer?
    #[test]
    fn should_return_error_if_eol_in_string_literal() {
        let mut lexer = lexer!("\"Hello World"); // <-- no closing quote
        assert_err!(
            lexer.consume_token(),
            SyntaxErrorKind::LineEndedDuringString,
            12,
            12,
            0
        )
    }

    /// Comments should be completely ignored by the lexer, they aren't part of the code.
    #[test]
    fn should_ignore_comment() {
        let mut lexer = lexer!("// This is a comment");
        assert_eq!(Token::EndOfFile, lexer.consume_token().unwrap())
    }

    /// Similarly, whitespace is not relevant to parsing so should be ignored.
    #[test]
    fn should_ignore_whitespace() {
        let mut lexer = lexer!("     ");
        assert_eq!(Token::EndOfLine, lexer.consume_token().unwrap())
    }

    #[test]
    fn should_return_correct_integer_literal() {
        let mut lexer = lexer!("56");
        assert_eq!(Token::IntegerLiteral(56), lexer.consume_token().unwrap())
    }

    #[test]
    fn should_return_correct_real_literal() {
        let mut lexer = lexer!("7.345");
        assert_eq!(Token::RealLiteral(7.345), lexer.consume_token().unwrap());
    }

    /// Although not listed in the specification, we will allow this explicitly
    #[test]
    fn should_parse_decimals_without_integer_section() {
        let mut lexer = lexer!(".5");
        assert_eq!(Token::RealLiteral(0.5), lexer.consume_token().unwrap());
    }

    /// Although not listed in the specification, we will allow this explicitly
    #[test]
    fn should_treat_as_real_with_decimal_point() {
        let mut lexer = lexer!("6.");
        assert_eq!(Token::RealLiteral(6.0), lexer.consume_token().unwrap());
    }

    #[test]
    fn should_error_on_unidentified_char() {
        let mut lexer = lexer!("¬");
        assert_err!(
            lexer.consume_token(),
            SyntaxErrorKind::UnrecognisedCharacter('¬'),
            0,
            0,
            0
        )
    }

    /// at_next_token is used for error handling, and the errors generated from these positions shouldn't include the whitespace before a token
    #[test]
    fn at_next_token_should_skip_whitespace() {
        let mut lexer = lexer!(" test");
        let pos = lexer.at_next_token();
        assert_eq!(1, pos.column());
        assert_eq!(0, pos.row());
    }

    /// Since [crate::file::LineHighlight]s are inclusive when passed positions, the last char of the token must be returned for error handling.
    #[test]
    fn at_last_token_should_return_last_char_of_last_token() {
        let mut lexer = lexer!(" test");
        lexer.consume_token().unwrap();
        let pos = lexer.at_last_token();
        assert_eq!(4, pos.column());
        assert_eq!(0, pos.row());
    }

    #[test]
    fn at_last_token_should_return_first_char_of_file_if_no_previous_token() {
        let lexer = lexer!("");
        let pos = lexer.at_last_token();
        assert_eq!(0, pos.column());
        assert_eq!(0, pos.row());
    }

    #[test]
    fn peek_token_should_not_advance() {
        let mut lexer = lexer!("!=");
        lexer.peek_token().unwrap();
        assert_eq!(Token::NotEquals, lexer.peek_token().unwrap());
    }

    #[test]
    fn consume_token_should_advance() {
        let mut lexer = lexer!("i +");
        lexer.consume_token().unwrap();
        assert_eq!(Token::Add, lexer.consume_token().unwrap());
    }

    /// At the end of each line, the lexer should automatically give `Token::EndOfLine`
    /// to indicate the end of the statement for the parser.
    /// When attempting to read a token out of bounds, the lexer will always return `Token::EndOfFile`.
    /// It was considered to use `Option<T>` for this purpose, but it produced a lot of bloat in parsing.
    #[test]
    fn should_return_end_of_line_or_file() {
        let mut lexer = lexer!("test\ntest");
        assert_ne!(Token::EndOfLine, lexer.consume_token().unwrap()); // test identifier
        assert_eq!(Token::EndOfLine, lexer.consume_token().unwrap()); // End of line
        assert_ne!(Token::EndOfLine, lexer.consume_token().unwrap()); // test identifier
        assert_eq!(Token::EndOfLine, lexer.consume_token().unwrap()); // End of line inserted by file creation
        for _ in 0..5 {
            // Subsequent token reads should all return EOF
            assert_eq!(Token::EndOfFile, lexer.consume_token().unwrap());
        }
    }
}

/// Map of keyword names to keywords
static RESERVED_IDENTIFIER_INDEX: phf::Map<&'static str, Token> = phf_map! {
    "array" => Token::Array,
    "procedure" => Token::Procedure,
    "endprocedure" => Token::EndProcedure,
    "function" => Token::Function,
    "endfunction" => Token::EndFunction,
    "const" => Token::Const,
    "global" => Token::Global,
    "for" => Token::For,
    "next" => Token::Next,
    "while" => Token::While,
    "endwhile" => Token::EndWhile,
    "do" => Token::Do,
    "until" => Token::Until,
    "if" => Token::If,
    "elseif" => Token::ElseIf,
    "else" => Token::Else,
    "endif" => Token::EndIf,
    "switch" => Token::Switch,
    "case" => Token::Case,
    "default" => Token::Default,
    "endswitch" => Token::EndSwitch,
    "return" => Token::Return,
    "true" => Token::BooleanLiteral(true),
    "false" => Token::BooleanLiteral(false),
    "then" => Token::Then,
    "to" => Token::To,
    "step" => Token::To,
    "DIV" => Token::Quotient,
    "MOD" => Token::Remainder,
    "OR" => Token::Or,
    "NOT" => Token::Not,
    "AND" => Token::And
};

/// Map of symbol strings to operator tokens
static OPERATOR_SEPARATOR_INDEX: phf::Map<&'static str, Token> = phf_map! {
    "!=" => Token::NotEquals,
    ">=" => Token::GreaterThanOrEquals,
    "<=" => Token::LessThanOrEquals,
    "==" => Token::Equals,
    "+" => Token::Add,
    "-" => Token::Subtract,
    "*" => Token::Multiply,
    "/" => Token::Divide,
    "^" => Token::Power,
    "=" => Token::Assign,
    ">" => Token::GreaterThan,
    "<" => Token::LessThan,
    "(" => Token::OpenBrace,
    ")" => Token::CloseBrace,
    "," => Token::Comma,
    "[" => Token::OpenSquareBrace,
    "]" => Token::CloseSquareBrace,
    "\n" => Token::EndOfLine
};

/// Standard implementation of a lexer.
#[derive(Clone)]
pub struct FileLexer {
    position: FilePosition,
    last_read: Option<Token>,
}

impl Lexer for FileLexer {
    fn at_next_token(&mut self) -> FilePosition {
        self.read_until_no_whitespace();
        self.position.clone()
    }

    fn at_last_token(&self) -> FilePosition {
        let mut copy = self.position.clone();
        copy.rewind_to_previous_char_if_possible();
        copy
    }

    fn peek_token(&mut self) -> Result<Token, SyntaxError> {
        let old_position = self.position.clone();
        let token = self.consume_token()?;
        self.position = old_position;

        Ok(token)
    }

    fn consume_token(&mut self) -> Result<Token, SyntaxError> {
        let token = self.read_token()?;
        self.last_read = Some(token.clone());
        Ok(token)
    }

    fn skip_to_newline(&mut self) {
        if self.position.column() != 0 {
            self.position.move_to_next_line();
        }
    }
}

impl FileLexer {
    /// Creates a new [FileLexer] that will begin reading tokens at the given position.
    ///
    /// # Arguments
    /// * `position` - The position within a file at which to start reading tokens.
    ///
    /// # Examples
    /// ```
    /// use erl_parser::FileLexer;
    /// let beginning = erl_parser::File::from_string("example = 5".to_owned()).beginning();
    ///
    /// let mut lexer = FileLexer::new(beginning);
    ///
    /// let ast = erl_parser::parser::parse_root_block(&mut lexer).unwrap();
    /// ```
    pub fn new(position: FilePosition) -> Self {
        Self {
            position,
            last_read: None,
        }
    }

    fn read_token(&mut self) -> Result<Token, SyntaxError> {
        self.read_until_no_whitespace();

        let before_token = self.position.clone();

        let first_char = match self.peek_char() {
            Some(char) => char,
            None => return Ok(Token::EndOfFile),
        };

        if first_char.is_digit(10) {
            return Ok(self.read_number_literal(false));
        }

        if first_char == '.' {
            let literal = self.read_number_literal(true);
            return Ok(if literal == Token::RealLiteral(0.0) {
                Token::Period
            } else {
                literal
            });
        }

        if is_allowed_for_beginning_of_identifier(first_char) {
            return Ok(self.read_identifier());
        }

        if first_char == '"' {
            self.read_char();
            return self.read_string_literal();
        }

        self.read_char();
        let second = self.peek_char();

        if let Some(second_char) = second {
            // Try to parse an operator based on both characters, e.g. `!=`
            let both = String::from_iter([first_char, second_char]);
            match OPERATOR_SEPARATOR_INDEX.get(&both) {
                Some(token) => {
                    self.read_char();
                    return Ok(token.clone());
                }
                None => {}
            };
        }

        match OPERATOR_SEPARATOR_INDEX.get(&first_char.to_string()) {
            Some(token) => return Ok(token.clone()),
            None => {}
        }

        return Err(SyntaxError::new(
            before_token.clone(),
            before_token,
            SyntaxErrorKind::UnrecognisedCharacter(first_char),
        ));
    }

    /// Reads characters until the next character would be the start of a token.
    fn read_until_no_whitespace(&mut self) {
        loop {
            match self.peek_char() {
                Some(c) => {
                    if c == '/' {
                        let before_comment = self.position.clone();
                        self.read_char();

                        if self.read_char() == Some('/') {
                            self.position.move_to_next_line();
                        } else {
                            self.position = before_comment;
                            return;
                        }
                    } else if !c.is_whitespace() || c == '\n' {
                        return;
                    }
                }
                None => return,
            }
            self.read_char();
        }
    }
    fn read_string_literal(&mut self) -> Result<Token, SyntaxError> {
        let mut str = String::new();

        loop {
            // Iterate characters until the end of the string (or the end of the file)
            match self.peek_char() {
                Some(c) => {
                    if c == '"' {
                        self.read_char();
                        return Ok(Token::StringLiteral(str));
                    } else if c != '\n' {
                        self.read_char();
                        str.push(c);
                        continue;
                    }
                }
                None => {}
            }

            let from = self.position.clone();
            let to = self.position.clone();
            return Err(SyntaxError::new(
                from,
                to,
                SyntaxErrorKind::LineEndedDuringString,
            ));
        }
    }

    fn read_number_literal(&mut self, mut is_after_decimal_point: bool) -> Token {
        let mut integer_portion = 0;
        let mut after_decimal_point: f64 = 0.0;
        let mut current_decimal_multiplier = 0.1;

        loop {
            // Find the next digit within the number literal
            let digit = match self.peek_char() {
                Some(c) => match c {
                    '0' => 0,
                    '1' => 1,
                    '2' => 2,
                    '3' => 3,
                    '4' => 4,
                    '5' => 5,
                    '6' => 6,
                    '7' => 7,
                    '8' => 8,
                    '9' => 9,
                    '.' => {
                        is_after_decimal_point = true;
                        self.read_char();
                        continue;
                    }
                    _ => break,
                },
                None => break, // End of file, so end of the literal
            };
            self.read_char();

            if is_after_decimal_point {
                after_decimal_point += digit as f64 * current_decimal_multiplier;
                current_decimal_multiplier /= 10.0;
            } else {
                integer_portion *= 10;
                integer_portion += digit;
            }
        }

        if is_after_decimal_point {
            Token::RealLiteral(integer_portion as f64 + after_decimal_point)
        } else {
            Token::IntegerLiteral(integer_portion)
        }
    }

    fn read_identifier(&mut self) -> Token {
        let mut str = String::new();

        // Keep parsing characters within the identifier until a special character is reached
        loop {
            match self.peek_char() {
                Some(c) => {
                    if is_allowed_for_identifier(c) {
                        str.push(c);
                    } else {
                        break;
                    }
                }
                None => break, // EOF also signifies the end of an identifier
            }
            self.read_char();
        }

        RESERVED_IDENTIFIER_INDEX
            .get(&str)
            .unwrap_or(&Token::Identifier(str))
            .clone()
    }

    /// Reads and returns the next character, then advances to the character after.
    /// Returns `None` if the next character would be outside the file.
    fn read_char(&mut self) -> Option<char> {
        let result = self.position.get_char();
        self.position.advance_to_next_char();
        result
    }

    /// Reads and returns the next character, without advancing to the character after.
    fn peek_char(&mut self) -> Option<char> {
        self.position.get_char()
    }
}

fn is_allowed_for_identifier(c: char) -> bool {
    c.is_alphabetic() || c.is_numeric() || c == '_'
}

fn is_allowed_for_beginning_of_identifier(c: char) -> bool {
    c.is_alphabetic()
}

#![forbid(unsafe_code)]
//! An incomplete parser for OCR Exam Reference Language.
//!
//! This parser is based upon the documentation for the language found [here](https://www.ocr.org.uk/Images/558027-specification-gcse-computer-science-j277.pdf), specifically section 3c on page 32. However, the specification can hardly be described as exhaustive, so this crate makes several assumptions about parts of the language.
//!
//! # Basic Usage
//! To get starting parsing code, use the [`parse_from_string`] function.
//! ```
//! let ast = erl_parser::parse_from_string("example = 5").unwrap();
//! ```
//!
//! Alternatively, to parse code from a file, use [`File::read`], along with [`parse_program`].
//! ```no_run
//! use erl_parser::File;
//! use std::path::PathBuf;
//!
//! let file = erl_parser::File::read(PathBuf::from("source_code.erl")).unwrap();
//! let ast = erl_parser::parse_program(file).unwrap();
//! ```
//!
//! # AST Examples
//! Below are some examples of parsing a program and checking the resulting AST.
//!
//! Hello World:
//! ```
//! use erl_parser::ast::*;
//!
//! assert_eq!(
//!     // Find the first statement in this file
//!     erl_parser::parse_from_string("print(\"Hello World!\")").unwrap()[0],
//!     RootStatement::Statement(Statement::Call(Call {
//!         // Calling the function `print`
//!         callee: Box::new(Callee::SubProgram("print".to_string())),
//!         // With argument `"Hello World"`
//!         args: vec![Expression::StringLiteral("Hello World!".to_string())]
//!     }))
//! )
//! ```
//!
//! Assigning a variable:
//! ```
//! use erl_parser::ast::*;
//!
//! assert_eq!(
//!     // Find the first statement in this file
//!     erl_parser::parse_from_string("i = 3").unwrap()[0],
//!     RootStatement::Statement(Statement::Assign {
//!         // Not declared as `const`, `global` or `array`
//!         is_const: false,
//!         is_global: false,
//!         is_array: false,
//!         to_assign: Assignable::Variable("i".to_string()), // Named `i`
//!         // Assigned to the expression `3`
//!         assign_with: AssignmentValue::Expression(Expression::IntegerLiteral(3))
//!     })
//! )
//!
//! ```
//!
//! Declaring a sub-program:
//! ```
//! use erl_parser::ast::*;
//!
//! assert_eq!(
//!     // Find the first statement in this file
//!     erl_parser::parse_from_string("
//!         function example(arg1)
//!             return 5
//!         endfunction",
//!     ).unwrap()[0],
//!     RootStatement::SubProgram {
//!         name: "example".to_string(),
//!         block: vec![Statement::Return { value: Some(Expression::IntegerLiteral(5)) }],
//!         argument_names: vec!["arg1".to_string()],
//!         is_function: true
//!     }
//! )
//! ```
//!
//! Creating an `if` statement:
//! ```
//! use erl_parser::ast::*;
//!
//! assert_eq!(
//!     erl_parser::parse_from_string("
//!         if name == \"Laurie\" then
//!             print(\"Nice name!\")
//!         endif
//!     ").unwrap()[0],
//!     // As we can see, the AST can get rather unwieldy to manually spell out ...
//!     RootStatement::Statement(Statement::If {
//!         segments: vec![ // Each segment represents an `if` or `elseif` portion of the `if` statement
//!             IfSegment { // We have no `elseif`, so there is only one segment
//!                 condition: Expression::Binary {
//!                     operator: BinaryOperator::Equals,
//!                     left: Box::new(Expression::Assignable(Assignable::Variable("name".to_string()))),
//!                     right: Box::new(Expression::StringLiteral("Laurie".to_string()))
//!                 },
//!                 block: vec![
//!                     Statement::Call(Call {
//!                         callee: Box::new(Callee::SubProgram("print".to_string())),
//!                         args: vec![Expression::StringLiteral("Nice name!".to_string())]
//!                     })
//!                 ]
//!             }],
//!         else_block: None // We have no `else` block
//!     })
//! )
//! ```

pub use err::{SyntaxError, SyntaxErrorKind};
pub use file::{File, FilePosition, LineHighlight};
pub use lexer::FileLexer;
pub use parser::parse_root_block;
pub use tokens::Token;

pub mod ast;
pub mod err;
pub mod file;
pub mod lexer;
pub mod parser;
pub mod tokens;

/// Parses a program from the given contents.
/// Returns `Ok` with the list of statements if all parsed successfully, or
/// `Err` with a [Vec] of all of the errors that occured if one or more statements failed to parse.
///
/// # Arguments
/// * `contents` - the source code to parse from.
///
/// # Examples
/// ```
/// let ast = erl_parser::parse_from_string("example = 5").unwrap();
/// ```
pub fn parse_from_string(
    contents: impl Into<String>,
) -> Result<Vec<ast::RootStatement>, Vec<err::SyntaxError>> {
    let file = File::from_string(contents.into());
    parse_program(file)
}

/// Parses a program from the given file.
///
/// Returns `Ok` with the list of statements if all parsed successfully, or
/// `Err` with a [Vec] of all of the errors that occured if one or more statements failed to parse.
///
/// # Arguments
/// * `file` - the file to parse from.
///
/// # Examples
/// ```
/// let file = erl_parser::File::from_string("example = 5".to_owned());
///
/// let ast = erl_parser::parse_program(file).unwrap();
/// ```
pub fn parse_program(file: File) -> Result<Vec<ast::RootStatement>, Vec<err::SyntaxError>> {
    let mut lexer = lexer::FileLexer::new(file.beginning());

    parser::parse_root_block(&mut lexer)
}

/// The lexer takes the ERL code and splits it up into tokens which are more easily processed by the parser.
pub trait Lexer: Clone {
    /// Returns the [FilePosition] at the start of the next token.
    fn at_next_token(&mut self) -> FilePosition;

    /// Returns the [FilePosition] at the end of the last token.
    fn at_last_token(&self) -> FilePosition;

    /// Parses and returns the next token, without advancing
    fn peek_token(&mut self) -> Result<Token, SyntaxError>;

    /// Parses and returns the next token, then moves to the token after that
    fn consume_token(&mut self) -> Result<Token, SyntaxError>;

    /// Moves the lexer to the position at the start of the next new line
    /// If already at the start of a line, this does nothing
    fn skip_to_newline(&mut self);
}

//! Types for handling errors during parsing.

use crate::{
    file::{FilePosition, LineHighlight},
    tokens::Token,
};
use std::fmt::{Debug, Display};

/// An error that occured while lexing or parsing, with its attached position
/// for reporting purposes.
///
/// The [Display] implementation for this error shows where in the file the error
/// occured, and uses coloured error messages.
#[derive(PartialEq)]
pub struct SyntaxError {
    tag: LineHighlight,
    kind: SyntaxErrorKind,
}

/// The type of [SyntaxError] that occured.
#[derive(Debug, PartialEq, Clone)]
pub enum SyntaxErrorKind {
    /// A binary operator token was expected, but a different token was provided
    ExpectedBinaryOperator,
    /// A unary operator token was expected, but a different token was provided
    ExpectedUnaryOperator,
    /// An identifier was expected, but a different token was provided
    ExpectedIdentifier,
    /// An expression was expected, but the sequence of tokens given couldn't be interpreted as any type of expression (even as an invalid expression)
    ExpectedExpression,
    /// One of the given tokens was expected
    ExpectedOneOf(Vec<Token>),
    /// A call operator was used on a sequence of tokens which isn't callable
    CannotCall,
    /// A statement was expected, but the sequence of tokens given couldn't be interpreted as any type of statement (even as an invalid statement)
    ExpectedStatement,
    /// The keywords given were invalid in the context
    UnexpectedKeyWords(Vec<Token>),
    /// An expression which is not a call expression was used as a statement
    CannotUseExpressionAsStatement,
    /// An expression which was assignable was used as a statement.
    CannotUseAssignableExpressionAsStatement,
    /// The current line ended during a string literal
    LineEndedDuringString,
    /// The given character was not recognised while parsing a token
    UnrecognisedCharacter(char),
}

impl SyntaxError {
    pub(crate) fn new(from: FilePosition, to: FilePosition, kind: SyntaxErrorKind) -> Self {
        Self {
            tag: LineHighlight::new(&from, &to),
            kind: kind,
        }
    }

    pub(crate) fn new_single(
        from: FilePosition,
        to: FilePosition,
        kind: SyntaxErrorKind,
    ) -> Vec<Self> {
        vec![Self::new(from, to, kind)]
    }

    /// Gets the type error that occured
    pub fn kind(&self) -> SyntaxErrorKind {
        self.kind.clone()
    }

    /// Returns a [LineHighlight] which shows where this error occured
    pub fn tag(&self) -> LineHighlight {
        self.tag.clone()
    }
}

impl Display for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.tag.display_msg(f, &self.kind)
    }
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl Display for SyntaxErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SyntaxErrorKind::ExpectedBinaryOperator => f.write_str("expected binary operator"),
            SyntaxErrorKind::ExpectedUnaryOperator => f.write_str("expected unary operator"),
            SyntaxErrorKind::ExpectedIdentifier => f.write_str("expected identifier"),
            SyntaxErrorKind::ExpectedExpression => f.write_str("expected expression"),
            SyntaxErrorKind::UnexpectedKeyWords(keywords) => {
                f.write_str("unexpected keyword")?;
                if keywords.len() > 1 {
                    f.write_str("s")?;
                }
                Ok(())
            },
            SyntaxErrorKind::ExpectedOneOf(tokens) => {
                if tokens.len() == 1 {
                    f.write_fmt(format_args!("expected `{}`", tokens[0]))
                }   else    {
                    f.write_str("expected one of: ")?;
                    for token in &tokens[0..tokens.len() - 1] {
                        f.write_fmt(format_args!("`{}`, ", token))?;
                    }
                    f.write_fmt(format_args!("or `{}`", tokens[tokens.len() - 1]))
                }
            },
            SyntaxErrorKind::CannotCall => f.write_str("cannot call this expression. (help: only identifiers, e.g. `print` or properties, e.g. `\"test\".substring` can be called)"),
            SyntaxErrorKind::ExpectedStatement => f.write_str("expected statement. (help: call expressions, assignments - with the `=` operator, `if` blocks, `while` and `for` loops and `return`s can all be used as statements)"),
            SyntaxErrorKind::CannotUseExpressionAsStatement => f.write_str("cannot use this expression type as a statement. (help: only call expressions can be used as statements, e.g. `print(\"Hello World\")`)"),
            SyntaxErrorKind::CannotUseAssignableExpressionAsStatement => f.write_str("cannot use this expression type as a statement. (help: did you mean to assign to this expression with the `=` operator?)"),
            SyntaxErrorKind::LineEndedDuringString => f.write_str("line (or file) cannot end in the middle of a string"),
            SyntaxErrorKind::UnrecognisedCharacter(char) => f.write_fmt(format_args!("unrecognised character {}", char))
        }
    }
}

//! Token are an abstraction over the source code that makes parsing less of a nightmare to implement.

use std::fmt::Display;

/// Represents a token, emitted by the lexer.
///
/// The documentation for each variant shows you what ERL construct it represents
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// A custom series of characters that can be interpreted in various ways, e.g. as a variable or function name
    Identifier(String),

    /// A string, e.g. `"Hello World"`
    StringLiteral(String),
    /// An integer, e.g. `5`
    IntegerLiteral(i64),
    /// A boolean, e.g. `true` or `false`
    BooleanLiteral(bool),
    /// A real number, e.g. `5.5`
    RealLiteral(f64),

    /// `(`
    OpenBrace,
    /// `)`
    CloseBrace,
    /// `[`
    OpenSquareBrace,
    /// `]`
    CloseSquareBrace,
    /// The end of a line of code. Should only be returned by a lexer once per CRLF or LF.
    EndOfLine,
    /// Returned if parsing a token outside a file.
    EndOfFile,
    /// `,`
    Comma,
    /// `then`
    Then,
    /// `.`
    Period,
    /// `step`
    Step,
    /// `to`
    To,
    /// `const`
    Const,
    /// `global`
    Global,
    /// `for`
    For,
    /// `next`
    Next,
    /// `while`
    While,
    /// `endwhile`
    EndWhile,
    /// `do`
    Do,
    /// `until`
    Until,
    /// `if`
    If,
    /// `elseif`
    ElseIf,
    /// `else`
    Else,
    /// `endif`
    EndIf,
    /// `switch`
    Switch,
    /// `case`
    Case,
    /// `default`
    Default,
    /// `endswitch`
    EndSwitch,
    /// `return`
    Return,
    /// `array`
    Array,
    /// `procedure`
    Procedure,
    /// `endprocedure`
    EndProcedure,
    /// `function`
    Function,
    /// `endfunction`
    EndFunction,
    /// `+`
    Add,
    /// `-`
    Subtract,
    /// `*`
    Multiply,
    /// `/`
    Divide,
    /// `^`
    Power,
    /// `>`
    GreaterThan,
    /// `>=`
    GreaterThanOrEquals,
    /// `<`
    LessThan,
    /// `<=`
    LessThanOrEquals,
    /// `==`
    Equals,
    /// `!=`
    NotEquals,
    /// `DIV`
    Quotient,
    /// `MOD`
    Remainder,
    /// `NOT`
    Not,
    /// `AND`
    And,
    /// `OR`
    Or,
    /// `=`
    Assign,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::StringLiteral(str) => f.write_fmt(format_args!("\"{}\"", str)),
            Token::IntegerLiteral(int) => f.write_fmt(format_args!("{}", int)),
            Token::BooleanLiteral(bool) => f.write_fmt(format_args!("{}", bool)),
            Token::RealLiteral(real) => f.write_fmt(format_args!("{}", real)),
            Token::Array => f.write_str("array"),
            Token::Procedure => f.write_str("procedure"),
            Token::EndProcedure => f.write_str("endprocedure"),
            Token::Function => f.write_str("function"),
            Token::EndFunction => f.write_str("endfunction"),
            Token::Const => f.write_str("const"),
            Token::Global => f.write_str("global"),
            Token::For => f.write_str("for"),
            Token::Next => f.write_str("next"),
            Token::While => f.write_str("while"),
            Token::EndWhile => f.write_str("endwhile"),
            Token::Do => f.write_str("do"),
            Token::Until => f.write_str("until"),
            Token::If => f.write_str("if"),
            Token::ElseIf => f.write_str("elseif"),
            Token::Else => f.write_str("else"),
            Token::EndIf => f.write_str("endif"),
            Token::Switch => f.write_str("switch"),
            Token::Case => f.write_str("case"),
            Token::Default => f.write_str("default"),
            Token::EndSwitch => f.write_str("endswitch"),
            Token::Return => f.write_str("return"),
            Token::OpenBrace => f.write_str("("),
            Token::CloseBrace => f.write_str(")"),
            Token::OpenSquareBrace => f.write_str("["),
            Token::CloseSquareBrace => f.write_str("]"),
            Token::EndOfLine => f.write_str("<end of line>"),
            Token::Comma => f.write_str(","),
            Token::Then => f.write_str("then"),
            Token::Period => f.write_str("."),
            Token::Assign => f.write_str("="),
            Token::Step => f.write_str("step"),
            Token::To => f.write_str("to"),
            Token::Add => f.write_str("+"),
            Token::Subtract => f.write_str("-"),
            Token::Multiply => f.write_str("*"),
            Token::Divide => f.write_str("/"),
            Token::Power => f.write_str("^"),
            Token::GreaterThan => f.write_str(">"),
            Token::GreaterThanOrEquals => f.write_str(">="),
            Token::LessThan => f.write_str("<"),
            Token::LessThanOrEquals => f.write_str("<="),
            Token::Equals => f.write_str("=="),
            Token::NotEquals => f.write_str("!="),
            Token::Quotient => f.write_str("DIV"),
            Token::Remainder => f.write_str("MOD"),
            Token::Not => f.write_str("NOT"),
            Token::And => f.write_str("AND"),
            Token::Or => f.write_str("OR"),
            Token::Identifier(str) => f.write_str(str),
            Token::EndOfFile => f.write_str("<EOF>"),
        }
    }
}

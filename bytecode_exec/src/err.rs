//! Runtime error handle types.
//!
//! The types in this module represent the possible runtime errors that could occur
//! after the AST is generated.

use std::fmt::Display;

use erl_parser::ast::{BinaryOperator, UnaryOperator};

use crate::stdlib::{Type, Value};

/// An error that can occur while executing an ERL program.
#[derive(Clone, Debug, PartialEq)]
pub enum RuntimeError {
    /// Thrown if declaring a variable as `global` in the global scope (main function).
    CannotUseGlobalKeywordInGlobalScope,
    /// Thrown if attempting to assign to a `const` variable.
    CannotAssignConstant(String),
    /// Thrown if attempting to declare a variable with the `const` or `array` keywords, and a variable of that name already exists.
    CannotRedeclareVariable(String),
    /// Thrown if attempting to get the value of a variable that does not exist.
    NoSuchVariable(String),
    /// Thrown if attempting to use the return value of a procedure as part of an expression.
    /// (this is not legal as procedures do not return a value)
    CannotUseProcedureInExpression(String),
    /// Thrown if using the syntax `return x` in a procedure.
    CannotReturnValueFromProcedure,
    /// Thrown if reaching the end of a function without returning a value, or returning early from a function without giving
    /// a return value.
    MustReturnValueFromFunction,
    /// Thrown if calling a sub-program that does not exist.
    NoSuchSubProgram(String),
    /// Thrown if calling a sub-program with the wrong number of arguments.
    WrongNumberOfArguments {
        /// The name of the sub-program passed the wrong number of arguments
        name: String,
        /// The number of arguments of the sub-program.
        expected: usize,
        /// The number of arguments passed to it in the AST.
        actual: usize,
    },
    /// Thrown if declaring a sub-program with a name that already exists.
    DuplicateSubProgramName(String),
    /// Thrown if an incorrect type is given to a function or operation.
    WrongType {
        /// The type that was expected.
        ///
        /// TODO: For performance reasons, right now there is no `actual` field here.
        expected: Type,
    },
    /// Thrown if failing to convert between two types
    FailedToConvert {
        /// The value being converted
        value: Value,
        /// The [crate::stdlib::Type] it was being converted to.
        converting_to: Type,
    },
    /// Thrown if given the incorrect types for a binary operation.
    CannotBinaryOperate(BinaryOperator),
    /// Thrown if given the incorrect types for a unary operation.
    CannotUnaryOperate(UnaryOperator),
    /// Thrown if IO fails
    IOError(String),
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::CannotUseGlobalKeywordInGlobalScope => f.write_str("cannot declare a variable using the `global` keyword in the global scope - since this is implied"),
            RuntimeError::CannotAssignConstant(name) => f.write_fmt(format_args!("cannot change the value of `const` variable `{name}`")),
            RuntimeError::CannotRedeclareVariable(name) => f.write_fmt(format_args!("cannot name a variable `{name}`, as a variable with that name already exists")),
            RuntimeError::NoSuchVariable(name) => f.write_fmt(format_args!("cannot access variable `{name}` as it does not exist")),
            RuntimeError::CannotUseProcedureInExpression(name) => f.write_fmt(format_args!("cannot use return value of procedure `{name}` as part of an expression")),
            RuntimeError::NoSuchSubProgram(name) => f.write_fmt(format_args!("cannot call sub-program `{name}` as it does not exist")),
            RuntimeError::WrongNumberOfArguments { name, expected, actual } => f.write_fmt(format_args!("wrong number of arguments for sub-program `{name}`. expected: {expected}, actual: {actual}")),
            RuntimeError::DuplicateSubProgramName(name) => f.write_fmt(format_args!("cannot name a sub-program `{name}`, as a sub-program with that name already exists")),
            RuntimeError::WrongType { expected } => f.write_fmt(format_args!("wrong type. expected: `{expected}`")),
            RuntimeError::CannotBinaryOperate(operation) => f.write_fmt(format_args!("cannot perform operation `{operation:?}` on the given types")),
            RuntimeError::CannotUnaryOperate(operation) => f.write_fmt(format_args!("cannot perform operation `{operation:?}` on the given type")),
            RuntimeError::FailedToConvert { value, converting_to } => f.write_fmt(format_args!("could not convert value `{value}` to type `{converting_to}`")),
            RuntimeError::IOError(msg) => f.write_fmt(format_args!("IO Failed: {msg}")),
            RuntimeError::CannotReturnValueFromProcedure => f.write_str("cannot return a value from a procedure"),
            RuntimeError::MustReturnValueFromFunction => f.write_str("cannot exit a function without returning a value"),
        }
    }
}

impl From<std::io::Error> for RuntimeError {
    fn from(err: std::io::Error) -> Self {
        Self::IOError(err.to_string())
    }
}

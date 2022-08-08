#![deny(unsafe_op_in_unsafe_fn)]

//! An stack-based virtual machine for executing OCR Exam Reference Language.
//!
//! # Examples
//!
//!
//! # Architecture
//! This executor is *stack-based*, so nearly all operations read from or write to the virtual stack.
//!

use std::fmt::Display;

use err::RuntimeError;
use rcstr::RcStr;

pub mod bytecode;
pub mod compiler;
pub mod err;
pub mod executor;
pub mod rcstr;
pub mod stack;
pub mod stdlib;

pub use compiler::Compiler;

#[cfg(test)]
mod tests {
    use crate::rcstr::RcStr;

    use super::*;

    /// Value size is very important for interpreter performance, avoid a regression.
    #[test]
    #[cfg(target_arch = "x86_64")]
    fn value_size_should_be_sixteen_bytes_or_less() {
        assert!(std::mem::size_of::<Value>() <= 16)
    }

    #[test]
    fn value_type_should_give_correct_type() {
        assert_eq!(Type::Integer, Value::Integer(5).r#type());
        assert_eq!(Type::Real, Value::Real(2.5).r#type());
        assert_eq!(Type::Boolean, Value::True.r#type());
        assert_eq!(Type::Boolean, Value::False.r#type());
        assert_eq!(Type::String, Value::String(RcStr::new("example")).r#type());
    }
}

/// Any value with the language at runtime.
#[derive(Debug, PartialEq)]
pub enum Value {
    /// Integer values
    Integer(i64),
    /// Real values, represented as floating point
    Real(f64),
    /// `true` boolean value
    True,
    /// `false` boolean value
    False,
    /// String values
    String(RcStr),
}

// Optimised clone implementation
impl Clone for Value {
    #[inline(always)]
    fn clone(&self) -> Self {
        match self {
            Self::String(string) => Self::String(string.clone()),
            // Using `ptr::read` here provideed a 6-7% speedup in some benchmarks compared to the default clone impl
            // SAFETY: All other variants of `Value` can be safely copied.
            _ => unsafe { std::ptr::read(self as *const Value) },
        }
    }
}

impl Value {
    pub fn r#type(&self) -> Type {
        match self {
            Self::Integer(_) => Type::Integer,
            Self::Real(_) => Type::Real,
            Self::String(_) => Type::String,
            Self::True => Type::Boolean,
            Self::False => Type::Boolean,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Integer(int) => f.write_fmt(format_args!("{int}")),
            Value::Real(real) => f.write_fmt(format_args!("{real}")),
            Value::String(string) => f.write_fmt(format_args!("{string}")),
            Value::True => f.write_str("true"),
            Value::False => f.write_str("false"),
        }
    }
}

impl TryInto<i64> for Value {
    type Error = RuntimeError;

    #[inline(always)]
    fn try_into(self) -> Result<i64, Self::Error> {
        match self {
            Value::Integer(int) => Ok(int),
            _ => Err(RuntimeError::WrongType {
                expected: Type::Integer,
            }),
        }
    }
}

impl TryInto<f64> for Value {
    type Error = RuntimeError;

    #[inline(always)]
    fn try_into(self) -> Result<f64, Self::Error> {
        match self {
            Value::Real(real) => Ok(real),
            _ => Err(RuntimeError::WrongType {
                expected: Type::Real,
            }),
        }
    }
}

impl TryInto<bool> for Value {
    type Error = RuntimeError;

    #[inline(always)]
    fn try_into(self) -> Result<bool, Self::Error> {
        match self {
            Value::True => Ok(true),
            Value::False => Ok(false),
            _ => Err(RuntimeError::WrongType {
                expected: Type::Boolean,
            }),
        }
    }
}

impl TryInto<RcStr> for Value {
    type Error = RuntimeError;

    fn try_into(self) -> Result<RcStr, Self::Error> {
        match self {
            Value::String(string) => Ok(string),
            _ => Err(RuntimeError::WrongType {
                expected: Type::String,
            }),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
/// The data type of a particular [Value].
/// Used primarily for error handling purposes.
pub enum Type {
    /// Integer type.
    Integer,
    /// Real/floating point type.
    Real,
    /// String type.
    String,
    /// `true` or `false` type.
    Boolean,
}

impl Display for Type {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Integer => f.write_str("integer"),
            Type::Real => f.write_str("real"),
            Type::String => f.write_str("string"),
            Type::Boolean => f.write_str("boolean"),
        }
    }
}

#[macro_export]
macro_rules! args {
    ($stack:ident, $arg:ident:$type:ty $(, $next_arg:ident:$next_type:ty)*) => {
        // SAFETY: The caller must verify there is enough space on the stack for the correct number of arguments to be popped
        let $arg = TryInto::<$type>::try_into($stack.pop_unchecked())?;
        $crate::args!($stack $(,$next_arg:$next_type)*);
    };
    ($stack:ident) => ()
}

#[macro_export]
macro_rules! count_args {
    ($arg:ident:$type:ty $(,$next_arg:ident:$next_type:ty)*) => {
        1usize + $crate::count_args!($($next_arg:$next_type),*)
    };
    () => (0usize)
}

/// Macro for wrapping native sub-programs to be called by the interpreter.
#[macro_export]
macro_rules! expose {
    (fn $name:ident($($next_arg:ident:$next_type:ty),*) -> Result<(), RuntimeError> $block:block) => {
        (
            stringify!($name).to_string(),
            // SAFETY:  The `arg_count` passed is equal to the number of arguments popped by the `args!` macro when
            // calling this native sub-program.
            // `is_function` is `false`, so no return value has to be pushed to stack.
            unsafe { $crate::bytecode::NativeCallInfo::new(
                $crate::count_args!($($next_arg:$next_type),*),
                false,
                Box::new(move |stack| {
                    $crate::args!(stack $(,$next_arg:$next_type)*);
                    let result: Result<(), $crate::err::RuntimeError> = { $block };

                    result
                })
            ) }
        )
    };
    (fn $name:ident($($next_arg:ident:$next_type:ty),*) -> Result<Value, RuntimeError> $block:block) => {
        (
            stringify!($name).to_string(),
            // SAFETY:  The `arg_count` passed is equal to the number of arguments popped by the `args!` macro when
            // calling this native sub-program.
            // `is_function` is `true`, which is safe as we push a return value to the stack before returning `Ok`.
            unsafe { $crate::bytecode::NativeCallInfo::new(
                $crate::count_args!($($next_arg:$next_type),*),
                true,
                Box::new(move |stack| {
                    $crate::args!(stack $(,$next_arg:$next_type)*);
                    let result: Result<$crate::stdlib::Value, $crate::err::RuntimeError> = { $block };
                    stack.push_unchecked(result?);

                    Ok(())
                })
            ) }
        )
    };
    (fn $name:ident($($next_arg:ident:$next_type:ty),*) -> Value $block:block) => {
        (
            // SAFETY:  The `arg_count` passed is equal to the number of arguments popped by the `args!` macro when
            // calling this native sub-program.
            // `is_function` is `true`, which is safe as a return value will always be pushed to stack if the function
            // returns `Ok`
            stringify!($name).to_string(),
            unsafe { $crate::bytecode::NativeCallInfo::new(
                $crate::count_args!($($next_arg:$next_type),*),
                true,
                Box::new(move |stack| {
                    $crate::args!(stack $(,$next_arg:$next_type)*);
                    let result: $crate::stdlib::Value = { $block };
                    stack.push_unchecked(result);

                    Ok(())
                })
            ) }
        )
    };
    (fn $name:ident($($next_arg:ident:$next_type:ty),*) $block:block) => {
        (
            stringify!($name).to_string(),

            // SAFETY:  The `arg_count` passed is equal to the number of arguments popped by the `args!` macro when
            // calling this native sub-program.
            // `is_function` is `false`, so we do not need to push a return value to the stack
            unsafe { $crate::bytecode::NativeCallInfo::new(
                $crate::count_args!($($next_arg:$next_type),*),
                false,
                Box::new(move |stack| {
                    $crate::args!(stack $(,$next_arg:$next_type)*);
                    let _result: () = { $block };

                    Ok(())
                })
            ) }
        )
    };
}

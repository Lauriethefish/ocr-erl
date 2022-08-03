//! The standard library for this VM.
//!
//! This module defines the functions available to the running ERL programs,
//! and also defines the type system, with the enums [Value] and [Type].

use crate::bytecode::NativeSubProgramPtr;
use crate::err::RuntimeError;

use crate::rcstr::RcStr;
use phf::phf_map;

use std::fmt::{Debug, Display};
use std::io::Write;

#[cfg(test)]
mod tests {
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
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// Integer values
    Integer(i64),
    /// Real values, represented as floating point
    Real(f64),
    /// String values
    String(RcStr),
    /// `true` boolean value
    True,
    /// `false` boolean value
    False,
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

trait ConvertArg<T> {
    fn try_into(self) -> Result<T, RuntimeError>;
}

impl ConvertArg<Value> for Value {
    #[inline(always)]
    fn try_into(self) -> Result<Value, RuntimeError> {
        Ok(self)
    }
}

impl ConvertArg<i64> for Value {
    #[inline(always)]
    fn try_into(self) -> Result<i64, RuntimeError> {
        match self {
            Value::Integer(int) => Ok(int),
            _ => Err(RuntimeError::WrongType {
                expected: Type::Integer,
            }),
        }
    }
}

impl ConvertArg<f64> for Value {
    #[inline(always)]
    fn try_into(self) -> Result<f64, RuntimeError> {
        match self {
            Value::Real(real) => Ok(real),
            _ => Err(RuntimeError::WrongType {
                expected: Type::Real,
            }),
        }
    }
}

impl ConvertArg<bool> for Value {
    #[inline(always)]
    fn try_into(self) -> Result<bool, RuntimeError> {
        match self {
            Value::True => Ok(true),
            Value::False => Ok(false),
            _ => Err(RuntimeError::WrongType {
                expected: Type::Boolean,
            }),
        }
    }
}

impl ConvertArg<RcStr> for Value {
    fn try_into(self) -> Result<RcStr, RuntimeError> {
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

/// Information required to call a native sub-program.
#[derive(Copy, Clone)]
pub(crate) struct NativeCallInfo {
    /// The number of arguments in the native sub-program.
    pub(crate) arg_count: usize,
    /// Whether the sub-program is a function (returns a value).
    pub(crate) is_function: bool,
    /// The pointer to call the sub-program. (the sub-program itself manages properly popping arguments from the stack).
    pub(crate) ptr: NativeSubProgramPtr,
}

macro_rules! func_args {
    ($stack:ident, $arg:ident:$type:ty $(, $next_arg:ident:$next_type:ty)*) => {
        let $arg = ConvertArg::<$type>::try_into($stack.pop())?;
        func_args!($stack $(,$next_arg:$next_type)*);
    };
    ($stack:ident) => ()
}

macro_rules! count_args {
    ($arg:ident:$type:ty $(,$next_arg:ident:$next_type:ty)*) => {
        1usize + count_args!($($next_arg:$next_type),*)
    };
    () => (0usize)
}

macro_rules! erl_func {
    (($($next_arg:ident:$next_type:ty),*), $code:block) =>
        {
            NativeCallInfo {
                ptr: NativeSubProgramPtr(|stack| {
                    func_args!(stack, $($next_arg:$next_type),*);
                    let result: Result<Value, RuntimeError> = { $code };
                    stack.push(result?);

                    Ok(())
                }),
                is_function: true,
                arg_count: count_args!($($next_arg:$next_type),*)
            }
        };
}

macro_rules! erl_proc {
    (($($next_arg:ident:$next_type:ty),*), $code:block) =>
        {
            NativeCallInfo {
                ptr: NativeSubProgramPtr(|stack| {
                    func_args!(stack, $($next_arg:$next_type),*);
                    let result: Result<(), RuntimeError> = { $code };

                    result
                }),
                is_function: false,
                arg_count: count_args!($($next_arg:$next_type),*)
            }
        };
}

#[allow(unused)]
pub(crate) const BUILT_IN_SUB_PROGRAMS: phf::Map<&'static str, NativeCallInfo> = phf_map! {
    "print" => erl_proc!((value: Value), {
        println!("{}", value);

        Ok(())
    }),
    "input" => erl_func!((prompt: Value), {
        print!("{}", prompt);
        std::io::stdout().flush()?;

        let mut text = String::new();

        std::io::stdin().read_line(&mut text)?;
        Ok(Value::String(RcStr::new(&text)))
    }),
    "int" => erl_func!((value: Value), {
        match value {
            Value::Integer(int) => Ok(Value::Integer(int)),
            Value::Real(real) => Ok(Value::Integer(real as i64)),
            Value::String(string) => match string.parse::<i64>() {
                Ok(int) => Ok(Value::Integer(int)),
                Err(_) => return Err(RuntimeError::FailedToConvert { value: Value::String(string), converting_to: Type::Integer }),
            },
            Value::True => Err(RuntimeError::FailedToConvert { value: Value::True, converting_to: Type::Integer }),
            Value::False => Err(RuntimeError::FailedToConvert { value: Value::False, converting_to: Type::Integer }),
        }
    }),
    "bool" => erl_func!((value: Value), {
        match value {
            Value::True => Ok(Value::True),
            Value::False => Ok(Value::False),
            Value::String(string) if string.eq_ignore_ascii_case("true") => Ok(Value::True),
            Value::String(string) if string.eq_ignore_ascii_case("false") => Ok(Value::False),
            _ => Err(RuntimeError::FailedToConvert { value, converting_to: Type::Boolean })
        }
    }),
    "str" => erl_func!((value: Value), {
        match value {
            Value::String(string) => Ok(Value::String(string)),
            _ => Ok(Value::String(RcStr::new(&value.to_string())))
        }
    }),
    "real" => REAL_CONVERTER,
    "float" => REAL_CONVERTER
};

const REAL_CONVERTER: NativeCallInfo = erl_func!((value: Value), {
    match value {
        Value::Integer(int) => Ok(Value::Real(int as f64)),
        Value::Real(real) => Ok(Value::Real(real)),
        Value::String(string) => match string.parse::<f64>() {
            Ok(real) => Ok(Value::Real(real)),
            Err(_) => {
                return Err(RuntimeError::FailedToConvert {
                    value: Value::String(string),
                    converting_to: Type::Real,
                })
            }
        },
        Value::True => Err(RuntimeError::FailedToConvert {
            value: Value::True,
            converting_to: Type::Integer,
        }),
        Value::False => Err(RuntimeError::FailedToConvert {
            value: Value::False,
            converting_to: Type::Integer,
        }),
    }
});

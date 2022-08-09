//! The standard library for this VM.
//!
//! This module defines the default functions available to an ERL program.

use crate::bytecode::NativeCallInfo;
use crate::err::RuntimeError;

use crate::rcstr::RcStr;
use crate::{expose, Type, Value};

use std::fmt::Arguments;
use std::io::{self, Write};
use std::rc::Rc;

/// Abstraction over IO for the standard library.
pub trait Io {
    /// Writes the given text to the console then ends the line.
    fn write_line_fmt(&self, args: Arguments) -> io::Result<()>;

    /// Prompts the user for input, with the given text as a prompt text.
    /// Returns the text entered by the user.
    fn prompt_fmt(&self, args: Arguments) -> io::Result<String>;
}

#[derive(Clone)]
struct StandardIo;

impl Io for StandardIo {
    fn write_line_fmt(&self, args: Arguments) -> io::Result<()> {
        let mut stdout = io::stdout();
        stdout.write_fmt(args)?;
        stdout.write_all(b"\n")?;
        Ok(())
    }

    fn prompt_fmt(&self, args: Arguments) -> io::Result<String> {
        let mut stdout = io::stdout();
        stdout.write_fmt(args)?;
        stdout.flush()?;

        let stdin = io::stdin();
        let mut result = String::new();

        stdin.read_line(&mut result)?;
        // Remove the LF or CRLF
        result.pop();
        if result.ends_with('\r') {
            result.pop();
        }
        Ok(result)
    }
}

/// Returns the standard library functions, using stdin and stdout for input/print.
pub fn with_default_io() -> Vec<(String, Rc<NativeCallInfo>)> {
    with_io(StandardIo {})
}

/// Returns the standard library functions, using the given streams for input/print.
#[rustfmt::skip]
pub fn with_io(io: impl Io + 'static + Clone) -> Vec<(String, Rc<NativeCallInfo>)> { 
    let print_io = io.clone();
    let input_io = io;


vec![

expose! {
    fn print(value: Value) -> Result<(), RuntimeError> {
        print_io.write_line_fmt(format_args!("{value}"))?;
        Ok(())
    }
},
expose! {
    fn input(prompt: Value) -> Result<Value, RuntimeError> {
        let text = input_io.prompt_fmt(format_args!("{prompt}"))?;

        Ok(Value::String(RcStr::new(&text)))
    }
},
expose! {
    fn int(value: Value) -> Result<Value, RuntimeError> {
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
    }
},
expose! {
    fn bool(value: Value) -> Result<Value, RuntimeError> {
        match value {
            Value::True => Ok(Value::True),
            Value::False => Ok(Value::False),
            Value::String(string) if string.eq_ignore_ascii_case("true") => Ok(Value::True),
            Value::String(string) if string.eq_ignore_ascii_case("false") => Ok(Value::False),
            _ => Err(RuntimeError::FailedToConvert { value, converting_to: Type::Boolean })
        }
    }
},
expose! {
    fn str(value: Value) -> Value {
        match value {
            Value::String(string) => Value::String(string),
            _ => Value::String(RcStr::new(&value.to_string()))
        }
    } 
},
expose!(
    fn real(value: Value) -> Result<Value, RuntimeError> {
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
            _ => Err(RuntimeError::FailedToConvert {
                value: Value::True,
                converting_to: Type::Real,
            })
        }
    }
)

]}

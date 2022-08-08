//! The standard library for this VM.
//!
//! This module defines the default functions available to an ERL program.

use crate::bytecode::NativeCallInfo;
use crate::err::RuntimeError;

use crate::rcstr::RcStr;
use crate::{expose, Type, Value};

use std::cell::RefCell;
use std::io::{BufRead, Write};
use std::rc::Rc;

/// Returns the standard library functions, using stdin and stdout for input/print.
pub fn with_default_io() -> Vec<(String, Rc<NativeCallInfo>)> {
    with_io(std::io::stdout(), std::io::stdin().lock())
}

/// Returns the standard library functions, using the given streams for input/print.
#[rustfmt::skip]
pub fn with_io(stdout: impl Write + 'static, stdin: impl BufRead + 'static) -> Vec<(String, Rc<NativeCallInfo>)> { 
    let stdout_print = Rc::new(RefCell::new(stdout));
    let stdout_input = stdout_print.clone();
    let stdin_input = Rc::new(RefCell::new(stdin));

vec![

expose! {
    fn print(value: Value) -> Result<(), RuntimeError> {
        writeln!(stdout_print.borrow_mut(), "{value}")?;
        Ok(())
    }
},
expose! {
    fn input(prompt: Value) -> Result<Value, RuntimeError> {
        writeln!(stdout_input.borrow_mut(), "{prompt}")?;
        stdout_input.borrow_mut().flush()?;

        let mut text = String::new();

        stdin_input.borrow_mut().read_line(&mut text)?;
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

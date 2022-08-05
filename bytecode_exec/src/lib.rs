#![deny(unsafe_op_in_unsafe_fn)]

//! An stack-based virtual machine for executing OCR Exam Reference Language.
//!
//! # Examples
//!
//!
//! # Architecture
//! This executor is *stack-based*, so nearly all operations read from or write to the virtual stack.
//!

use erl_parser::ast::RootStatement;
use err::RuntimeError;

pub mod bytecode;
pub mod compiler;
pub mod err;
pub mod executor;
pub mod rcstr;
mod stack;
pub mod stdlib;

/// Compiles the given AST into an ERL module and executes it.
pub fn compile_and_execute(ast: Vec<RootStatement>) -> Result<(), RuntimeError> {
    let module = compiler::compile(ast);
    executor::execute_main(&module)
}

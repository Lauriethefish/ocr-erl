//! The bytecode format used by the VM.

use std::fmt::Debug;

use crate::{err::RuntimeError, executor::Stack, rcstr::RcStr};

#[cfg(test)]
mod tests {
    use super::*;

    /// Instruction size is important for the performance of the interpreter.
    /// This avoids a regresssion.
    #[test]
    fn instruction_size_should_be_sixteen_bytes_or_less() {
        assert!(std::mem::size_of::<Instruction>() <= 16)
    }
}

/// A native-sub program pointer.
#[repr(transparent)]
#[derive(Copy, Clone)]
pub(crate) struct NativeSubProgramPtr(pub fn(&mut Stack) -> Result<(), RuntimeError>);

impl PartialEq for NativeSubProgramPtr {
    fn eq(&self, other: &Self) -> bool {
        self.0 as usize == other.0 as usize
    }
}

impl Debug for NativeSubProgramPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("<native function ptr>")
    }
}

/// Contains all of the compiled sub-programs within an ERL file.
#[derive(Clone)]
pub struct Module {
    /// The sub-programs within the ERL file.
    /// Sub-programs have no name at runtime - they are merely represented by indices.
    /// The last sub-program must always be the main procedure.
    pub(crate) sub_programs: Vec<SubProgram>,
}

impl Debug for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Module")
            .field("sub_programs", &self.sub_programs)
            .finish()
    }
}

/// A compiled ERL sub-program
#[derive(Clone, PartialEq)]
pub(crate) struct SubProgram {
    /// The number of local variables (including arguments) in the sub-program.
    /// The arguments are treated as locals starting at index 0.
    pub(crate) local_count: usize,

    /// The number of arguments of the sub-program.
    pub(crate) arg_count: usize,

    /// The instructions within the sub-program.
    pub(crate) instructions: Vec<Instruction>,

    /// If true, the sub-program's execution *must* finish with a `ReturnValue` instruction.
    /// If false, the sub-program's execution *must not* finish with a `ReturnValue` instruction.
    pub(crate) is_function: bool,
}

impl Debug for SubProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SubProgram")
            .field("local_count", &self.local_count)
            .field("arg_count", &self.arg_count)
            .field("instructions", &InstructionFormatter { sub_program: self })
            .field("is_function", &self.is_function)
            .finish()
    }
}

/// An instruction within the bytecode.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Instruction {
    /// Pops and adds the two values on the top of the stack, then pushes the result to the stack.
    Add,
    /// Pops and subtracts the top value of the stack from the value beneath it, then pushes the result to the stack.
    Subtract,
    /// Pops and multiples the two values on the top of the stack, then pushes the result to the stack
    Multiply,
    /// Pops the top value of the stack and the value beneath it. The value beneath is divided by the value at the top of the stack.
    /// The result is then pushed to the stack.
    /// The resulting value from this operation is always a real.
    Divide,
    /// Pops the top value of the stack and the value beneath it. The value beneath is divided by the value at the top of the stack.
    /// The remainder is then pushed to the stack.
    /// The resulting value from this operation is always an integer.
    Remainder,
    /// Pops the top value of the stack and the value beneath it. The value beneath is divided by the value at the top of the stack.
    /// The quotient is then pushed to the stack.
    /// The resulting value from this operation is always an integer.
    Quotient,
    /// Pops the top value of the stack and the value beneath it. The value beneath is raised to the power value at the top of the stack.
    /// The result is then pushed to the stack.
    Power,

    /// Pops two values at the top of the stack. The result is then pushed to the stack.
    GreaterThan,
    /// Pops two values at the top of the stack. The result is then pushed to the stack.
    GreaterThanOrEquals,
    /// Pops two values at the top of the stack. The result is then pushed to the stack.
    LessThan,
    /// Pops two values at the top of the stack. The result is then pushed to the stack.
    LessThanOrEquals,
    /// Pops two values from the top of the stack. The result is then pushed to the stack.
    Equals,
    /// Pops two values from the top of the stack. The result is then pushed to the stack.
    NotEquals,
    /// Pops a boolean value from the top of the stack, then pushes the opposite boolean value to the stack.
    Not,

    /// Pops the value from the top of the stack and jumps to the given index if it is `true`.
    JumpIfTrue(usize),
    /// Pops the value from the top of the stack and jumps to the given index if it is `false`.
    JumpIfFalse(usize),
    /// If the value at the top of the stack is `false`, jumps to the given index.
    /// If the value at the top of the stack is `true`, it is popped from the stack.
    /// This instruction is particularly useful for efficiently implementing conditional AND.
    JumpIfFalsePopIfTrue(usize),
    /// If the value at the top of the stack is `true`, jumps to the given index.
    /// If the value at the top of the stack is `false`, it is popped from the stack.
    /// This instruction is particularly useful for efficiently implementing conditional AND.
    JumpIfTruePopIfFalse(usize),

    /// Jumps to the given instruction index.
    Jump(usize),

    /// Calls the sub-program within the module with the given index.
    /// The arguments for the call must be pushed to the stack.
    /// When this instruction completes, the arguments will be popped off of the stack.
    /// If calling a function, the return value will be pushed to the stack.
    Call(usize),
    /// Calls the native sub-program with the given pointer.
    /// The arguments for the call must be pushed to the stack.
    /// When this instruction completes, the arguments will be popped off of the stack.
    /// If calling a function, the return value will be pushed to the stack.
    CallNative(NativeSubProgramPtr),
    /// Returns from the current function with no return value.
    Return,
    /// Returns the value at the top of stack from the current function.
    ReturnValue,

    /// Pushes the given integer to the stack.
    LoadInteger(i64),
    /// Pushes the given real to the stack.
    LoadReal(f64),
    /// Pushes `true` to the stack.
    LoadTrue,
    /// Pushes `false` to the stack.
    LoadFalse,
    /// Pushes the given string to the stack.
    LoadString(RcStr),
    /// Pushes the local with the given index to the stack.
    Load(usize),
    /// Pushes the global with the given index to the stack.
    /// It is important to note that globals in this interpreter are just locals of the main sub-program in [Module].
    /// Thus, in the main function, this instruction is identical to `Load(u16)`.
    LoadGlobal(usize),
    /// Pops and writes the value on the top of stack to the local with the given index.
    Save(usize),
    /// Pops and writes the value on the top of stack to the global with the given index.
    /// It is important to note that globals in this interpreter are just locals of the main sub-program in [Module].
    /// Thus, in the main function, this instruction is identical to `Save(u16)`.
    SaveGlobal(usize),
    /// Pops a value off of the top of the stack.
    Pop,

    /// Throws the given error.
    Throw(Box<RuntimeError>),

    /// Does nothing
    Nop,
}

struct InstructionFormatter<'a> {
    sub_program: &'a SubProgram,
}

impl Debug for InstructionFormatter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[ \n")?;
        for (idx, instruction) in self.sub_program.instructions.iter().enumerate() {
            f.write_fmt(format_args!("  {idx}: "))?;
            match instruction {
                Instruction::Add => f.write_str("ADD"),
                Instruction::Subtract => f.write_str("SUB"),
                Instruction::Multiply => f.write_str("MUL"),
                Instruction::Divide => f.write_str("DIV"),
                Instruction::Remainder => f.write_str("REM"),
                Instruction::Quotient => f.write_str("QOT"),
                Instruction::Power => f.write_str("POW"),
                Instruction::GreaterThan => f.write_str("GTN"),
                Instruction::GreaterThanOrEquals => f.write_str("GOE"),
                Instruction::LessThan => f.write_str("LTN"),
                Instruction::LessThanOrEquals => f.write_str("LOE"),
                Instruction::Equals => f.write_str("EQL"),
                Instruction::NotEquals => f.write_str("NEQ"),
                Instruction::Not => f.write_str("NOT"),
                Instruction::JumpIfTrue(to_idx) => f.write_fmt(format_args!("JIT, idx: {to_idx}")),
                Instruction::JumpIfFalse(to_idx) => f.write_fmt(format_args!("JIF, idx: {to_idx}")),
                Instruction::JumpIfFalsePopIfTrue(to_idx) => {
                    f.write_fmt(format_args!("PJF, idx: {to_idx}"))
                }
                Instruction::JumpIfTruePopIfFalse(to_idx) => {
                    f.write_fmt(format_args!("PJT, idx: {to_idx}"))
                }
                Instruction::Jump(to_idx) => f.write_fmt(format_args!("JMP, idx: {to_idx}")),
                Instruction::Call(call_idx) => f.write_fmt(format_args!("CLL, idx: {call_idx}")),
                Instruction::CallNative(_) => f.write_str("CLN"),
                Instruction::Return => f.write_str("RET"),
                Instruction::ReturnValue => f.write_str("RTV"),
                Instruction::LoadInteger(int) => f.write_fmt(format_args!("LIN, {int}")),
                Instruction::LoadReal(real) => f.write_fmt(format_args!("LRL, {real}")),
                Instruction::LoadTrue => f.write_str("LTR"),
                Instruction::LoadFalse => f.write_str("LFL"),
                Instruction::LoadString(string) => f.write_fmt(format_args!("LSR, \"{string}\"")),
                Instruction::Load(local_idx) => f.write_fmt(format_args!("LLC, idx: {local_idx}")),
                Instruction::LoadGlobal(global_idx) => {
                    f.write_fmt(format_args!("LGL, idx: {global_idx}"))
                }
                Instruction::Save(local_idx) => f.write_fmt(format_args!("SLC, idx: {local_idx}")),
                Instruction::SaveGlobal(global_idx) => {
                    f.write_fmt(format_args!("SGL, idx: {global_idx}"))
                }
                Instruction::Pop => f.write_str("POP"),
                Instruction::Throw(err) => f.write_fmt(format_args!("THW, {err}")),
                Instruction::Nop => f.write_str("NOP"),
            }?;

            f.write_str(",\n")?;
        }
        f.write_str("]")?;

        Ok(())
    }
}

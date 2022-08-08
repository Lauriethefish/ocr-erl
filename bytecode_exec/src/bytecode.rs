//! The bytecode format used by the VM.

use std::{fmt::Debug, rc::Rc};

use crate::{err::RuntimeError, rcstr::RcStr, stack::Stack};

#[cfg(test)]
mod tests {
    use super::*;

    /// Instruction size is important for the performance of the interpreter.
    /// This avoids a regresssion.
    #[test]
    #[cfg(target_arch = "x86_64")]
    fn instruction_size_should_be_sixteen_bytes_or_less() {
        assert!(std::mem::size_of::<Instruction>() <= 16)
    }
}

/// Contains all of the compiled sub-programs within an ERL file.
/// Encapsulates the compiled sub-programs, and runs checks to uphold certain guarantees about the instructions
/// within them. These guarantees are required for the executor to safely execute the bytecode.
///
/// # Instruction Guarantees
/// - For [Instruction]s `Add`, `Subtract`, `Multiply`, `Divide`, `Remainder`, `Quotient`, `Power`, `GreaterThan`,
/// `GreaterThanOrEquals`, `LessThan`, `LessThanOrEquals`, `Equals` and `NotEquals`, at least two values will be pushed
/// to stack by preceeding instructions.
/// - For [Instruction]s `Not`, `JumpIfTrue`, `JumpIfFalse`, `JumpIfFalsePopIfTrue`, `JumpIfTruePopIfFalse`,
///  `Save`, `PeekSave`, `SaveGlobal`, `Pop`, and `ReturnValue`, at least one value will be pushed to stack by preceeding instructions.
/// - For [`Instruction::Call`], the given sub-program index will return a valid sub-program when passed to [`Module::sub_program`]. It is also
/// guaranteed that at least [`SubProgram::arg_count`] values will be pushed to the stack by preceeding instructions.
/// - For [`Instruction::CallNative`], at least [`NativeCallInfo::arg_count`] values will be pushed to the stack by preceeding instructions.
/// - For [`Instruction::Load`], [`Instruction::Save`] and [`Instruction::PeekSave`] the given local index must be less than the [`SubProgram::local_count`] within the
/// sub-program when there instruction is invoked.
/// - For [`Instruction::LoadGlobal`] and [`Instruction::SaveGlobal`], the given global index must be less than the [`SubProgram::local_count`]
/// within the main procedure.
///
/// Additionally, none of the instructions will ever push more than [`SubProgram::max_stack_space`] - [`SubProgram::local_count`] values
/// to the stack in total. None of the instructions will ever pop a local off of the stack either.
#[derive(Clone, Debug)]
pub struct Module {
    /// The sub-programs within the ERL file.
    sub_programs: Vec<SubProgram>,

    /// The index of the main sub-program within the module.
    main_idx: usize,
}

impl Module {
    /// Creates a new [Module].
    ///
    /// # Arguments
    /// * `sub_programs` - the sub-programs within the module.
    /// * `main_idx` - the index of the main procedure within `sub_programs`.
    ///
    /// # Panics
    /// This function will panic if:
    /// * `main_idx` is out of bounds of `sub_programs`
    /// * `main_idx` points to a function.
    /// * `main_idx` points to a sub-program that has more than 0 arguments.
    /// * The instructions within the sub-programs do not uphold the guarantees specified in the documentation for [Module].
    pub(crate) fn new(mut sub_programs: Vec<SubProgram>, main_idx: usize) -> Module {
        let main = sub_programs
            .get(main_idx)
            .expect("The given `main_idx` was outside `sub_programs`");
        assert!(
            !main.is_function,
            "The sub-program pointed to by `main_idx` wasn't a procedure"
        );
        assert_eq!(
            main.arg_count, 0,
            "The sub-program pointed to by `main_idx` must have zero arguments"
        );

        for i in 0..sub_programs.len() {
            sub_programs[i].max_stack_space =
                Self::verify_sub_program(&sub_programs, &sub_programs[i], &sub_programs[main_idx]);
        }

        Module {
            sub_programs,
            main_idx,
        }
    }

    /// Checks the instructions within the given sub-program to verify that they uphold the guarantees specified in [Module].
    /// Returns the maximum stack space that could be required for the sub-program to run, including the locals.
    fn verify_sub_program(
        sub_programs: &[SubProgram],
        sub_program: &SubProgram,
        main: &SubProgram,
    ) -> usize {
        // Keeps track of the stack size before each instruction.
        // This allows us to make sure that each instruction is only reachable with one stack-size.
        // If `None` is the value for a given instruction index, this means that the instruction is yet to be reached.
        let mut stack_sizes_before_idx = vec![None; sub_program.instructions.len()];

        let mut size: isize = 0;
        let mut max_size: isize = size;

        let mut idx = 0;
        while idx < sub_program.instructions.len() {
            // Add the stack size before this instruction, or, if this instruction has already been jumped to
            // elsewhere, verify that the stack size after the jump matches the stack size at this point.
            Self::add_or_verify_size_matches(&mut stack_sizes_before_idx, idx, size);

            match &sub_program.instructions[idx] {
                Instruction::Add
                | Instruction::Subtract
                | Instruction::Multiply
                | Instruction::Divide
                | Instruction::Remainder
                | Instruction::Quotient
                | Instruction::Power
                | Instruction::GreaterThan
                | Instruction::GreaterThanOrEquals
                | Instruction::LessThan
                | Instruction::LessThanOrEquals
                | Instruction::Equals
                | Instruction::NotEquals => {
                    // All binary operators pop 2 operands and then push the result
                    // Note that we can NOT just use an overall diff of -1, since we need to verify that there are
                    // two values on the stack available to be popped.
                    Self::diff(&mut size, -2);
                    Self::diff(&mut size, 1);
                }
                Instruction::Not => {
                    // While the overall diff here is 0, we must verify that we
                    // can pop one value of the stack to perform the operation on.
                    Self::diff(&mut size, -1);
                    Self::diff(&mut size, 1);
                }
                Instruction::JumpIfTrue(to) | Instruction::JumpIfFalse(to) => {
                    Self::diff(&mut size, -1); // Popping off the `true`/`false` argument

                    // Make sure that the size of the stack before executing the instruction we're jumping to matches the stack size after this jump.
                    Self::add_or_verify_size_matches(&mut stack_sizes_before_idx, *to, size);
                }
                Instruction::JumpIfFalsePopIfTrue(to) | Instruction::JumpIfTruePopIfFalse(to) => {
                    // Make sure that the size of the stack before executing the instruction we're jumping to matches the stack size after this jump.
                    Self::add_or_verify_size_matches(&mut stack_sizes_before_idx, *to, size);
                    Self::diff(&mut size, -1); // If execution continues in the current path, the stack size will decrease by 1
                }
                Instruction::Jump(to) => {
                    // Make sure that the size of the stack before executing the instruction we're jumping to matches the stack size after this jump.
                    Self::add_or_verify_size_matches(&mut stack_sizes_before_idx, *to, size);
                }
                Instruction::Call(idx) => {
                    let to_call = sub_programs
                        .get(*idx)
                        .expect("Invalid sub-program idx in call");

                    // To call, we need at least the correct number of arguments on stack
                    Self::diff(&mut size, -(to_call.arg_count as isize));

                    // After a function call, an extra value is pushed to stack
                    if to_call.is_function {
                        Self::diff(&mut size, 1);
                    }
                }
                Instruction::CallNative(to_call) => {
                    // To call, we need at least the correct number of arguments on stack
                    Self::diff(&mut size, -(to_call.arg_count as isize));

                    // After a function call, an extra value is pushed to stack
                    if to_call.is_function {
                        Self::diff(&mut size, 1);
                    }
                }
                Instruction::Return => {}
                // Returning a value requires a value on the top of the stack to be popped.
                Instruction::ReturnValue => Self::diff(&mut size, -1),

                // Loading constants always pushes one value to stack.
                Instruction::LoadInteger(_)
                | Instruction::LoadReal(_)
                | Instruction::LoadTrue
                | Instruction::LoadFalse
                | Instruction::LoadString(_) => Self::diff(&mut size, 1),

                Instruction::Load(local_idx) => {
                    // Verify that the local_idx is within bounds
                    assert!(
                        *local_idx < sub_program.local_count,
                        "Local load out of range of `local_count` within the sub-program"
                    );
                    Self::diff(&mut size, 1);
                }
                Instruction::LoadGlobal(global_idx) => {
                    // Verify that the global_idx is within bounds
                    assert!(
                        *global_idx < main.local_count,
                        "Global load out of range of `local_count` within the main sub-program"
                    );
                    Self::diff(&mut size, 1);
                }

                Instruction::Save(local_idx) => {
                    // Verify that the local_idx is within bounds
                    assert!(
                        *local_idx < sub_program.local_count,
                        "Local save out of range of `local_count` within the sub-program"
                    );
                    Self::diff(&mut size, -1); // Make sure that enough stack space is available
                }
                Instruction::PeekSave(local_idx) => {
                    // Verify that the local_idx is within bounds
                    assert!(
                        *local_idx < sub_program.local_count,
                        "Local save out of range of `local_count` within the sub-program"
                    );
                    Self::diff(&mut size, -1); // Make sure that enough stack space is available
                    Self::diff(&mut size, 1); // The value isn't actually popped from stack.
                }
                Instruction::SaveGlobal(global_idx) => {
                    // Verify that the global_idx is within bounds
                    assert!(
                        *global_idx < main.local_count,
                        "Global load out of range of `local_count` within the main sub-program"
                    );
                    Self::diff(&mut size, -1); // Make sure that enough stack space is available
                }
                Instruction::Pop => Self::diff(&mut size, -1),
                Instruction::Throw(_) => {
                    // If an error instruction is found, the code path from this point onwards should be ignored.
                    // Thus, we will continue checking stack sizes at the next instruction that already has a stack size
                    // assigned, since this instruction must be reachable by a jump in the instructions already iterated.

                    idx += 1; // Run this first to skip the current instruction
                    while idx < sub_program.instructions.len() {
                        // Once we reach an instruction that could be jumped too, continue checking stack sizes at that point
                        if let Some(other_size) = stack_sizes_before_idx[idx] {
                            size = other_size; // Ignore the stack size after throwing
                            break;
                        }

                        idx += 1;
                    }

                    continue;
                }
                Instruction::Nop => {}
            };

            if size > max_size {
                max_size = size;
            }

            idx += 1;
        }

        // The maximum stack size from pushing instructions + the number of locals gives us how much space we need in total to call this function.
        (max_size as usize) + sub_program.local_count
    }

    fn add_or_verify_size_matches(sizes: &mut [Option<isize>], idx: usize, size: isize) {
        match sizes[idx] {
            Some(existing) => {
                if existing != size {
                    panic!("Instruction idx {idx} can be reached with multiple stack sizes!")
                }
            }
            None => sizes[idx] = Some(size),
        }
    }

    fn diff(size: &mut isize, diff: isize) {
        let new_size = size
            .checked_add(diff)
            .expect("Executing this code will result in a stack overflow!");
        assert!(
            new_size >= 0,
            "Executing this code will result in a stack underflow"
        );

        *size = new_size;
    }

    /// Gets the index of the main procedure within this [Module].
    pub(crate) fn main_idx(&self) -> usize {
        self.main_idx
    }

    /// Gets a reference to the main procedure within this [Module].
    pub(crate) fn main(&self) -> &SubProgram {
        &self.sub_programs[self.main_idx]
    }

    /// Gets a slice of all of the sub-programs within this [Module].
    pub(crate) fn sub_programs(&self) -> &[SubProgram] {
        &self.sub_programs
    }

    /// Gets a reference to the sub-program at index `idx`.
    pub(crate) fn sub_program(&self, idx: usize) -> &SubProgram {
        &self.sub_programs[idx]
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

    /// The maximum number of values on the stack that this function needs in order to execute.
    /// This includes the local variables (which includes the arguments).
    /// Do not worry about setting this field manually, it is automatically set when creating a [Module].
    pub(crate) max_stack_space: usize,

    /// The instructions within the sub-program.
    pub(crate) instructions: Vec<Instruction>,

    /// If true, the sub-program's execution *must* finish with a `ReturnValue` instruction.
    /// If false, the sub-program's execution *must not* finish with a `ReturnValue` instruction.
    pub(crate) is_function: bool,

    /// The name of the sub-program, for error reporting purposes.
    /// `None` if this is the main procedure.
    pub(crate) name: Option<String>,
}

impl Debug for SubProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SubProgram")
            .field("local_count", &self.local_count)
            .field("arg_count", &self.arg_count)
            .field("instructions", &InstructionsFormatter { sub_program: self })
            .field("is_function", &self.is_function)
            .field("max_stack_space", &self.max_stack_space)
            .finish()
    }
}

type NativeSubProgram = Box<dyn Fn(&mut Stack) -> Result<(), RuntimeError>>;

/// The information required for the compiler/executor to process a native sub-program.
pub struct NativeCallInfo {
    /// The number of arguments in the native sub-program.
    arg_count: usize,
    /// Whether the sub-program is a function (returns a value).
    is_function: bool,
    /// The pointer to call the sub-program. (the sub-program itself manages properly popping arguments from the stack and pushing the result).
    ptr: NativeSubProgram,
}

impl NativeCallInfo {
    /// Creates a new [NativeCallInfo].
    ///
    /// # Safety
    /// The given `ptr` must be a [NativeSubProgram] that (if returning `Ok`)
    /// pops exactly `arg_count` values from the stack. If `is_function` is `true`, then the
    /// function must also push exactly one return value to stack.
    ///
    /// If the sub-program does not do this, using this [NativeCallInfo] may lead to undefined behaviour.
    ///
    /// NOTE: This function is not intended to be used directl. Consider using the `expose!` macro.
    pub unsafe fn new(arg_count: usize, is_function: bool, ptr: NativeSubProgram) -> Rc<Self> {
        Rc::new(NativeCallInfo {
            arg_count,
            is_function,
            ptr,
        })
    }

    /// Calls the native sub-program.
    /// This will pop [`NativeCallInfo::arg_count`] values from the stack, and if [`NativeCallInfo::is_function`]
    /// is true, one return value will be pushed to stack
    ///
    /// # Safety
    /// At least [`NativeCallInfo::arg_count`] values must be pushed to stack before this call,
    /// otherwise the result is undefined behaviour. Additionally, if [`NativeCallInfo::arg_count`] is 0,
    /// and [`NativeCallInfo::is_function`] is `true`, the stack must NOT be full.
    #[inline(always)]
    pub(crate) unsafe fn call(&self, stack: &mut Stack) -> Result<(), RuntimeError> {
        (self.ptr)(stack)
    }

    /// Gets the number of arguments of the native sub-program
    #[inline(always)]
    pub(crate) fn arg_count(&self) -> usize {
        self.arg_count
    }

    /// Gets whether or not the native sub-program is a function (returns a value)
    #[inline(always)]
    pub(crate) fn is_function(&self) -> bool {
        self.is_function
    }
}

impl PartialEq for NativeCallInfo {
    fn eq(&self, other: &Self) -> bool {
        // TODO: This PartialEq implementation is not ideal, and is only intended for use in tests.
        // Use #[cfg(test)] here?
        self.arg_count == other.arg_count && self.is_function == other.is_function
        /* && self.ptr == other.ptr */
    }
}

/// An instruction within the bytecode.
#[derive(Clone, PartialEq)]
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

    /// Pops two values at the top of the stack.
    /// If the beneath value is greater than the top-of-stack value, `true` is pushed to stack.
    /// Otherwise, `false` is pushed to stack.
    GreaterThan,
    /// Pops two values at the top of the stack.
    /// If the beneath value is greater than or equal to the top-of-stack value, `true` is pushed to stack.
    /// Otherwise, `false` is pushed to stack.
    GreaterThanOrEquals,
    /// Pops two values at the top of the stack.
    /// If the beneath value is less than the top-of-stack value, `true` is pushed to stack.
    /// Otherwise, `false` is pushed to stack.
    LessThan,
    /// Pops two values at the top of the stack.
    /// If the beneath value is less than or equal to the top-of-stack value, `true` is pushed to stack.
    /// Otherwise, `false` is pushed to stack.
    LessThanOrEquals,
    /// Pops two values at the top of the stack.
    /// If they are equal, `true` is pushed to stack.
    /// Otherwise, `false` is pushed to stack.
    Equals,
    /// Pops two values at the top of the stack.
    /// If they are not equal, `true` is pushed to stack..
    /// Otherwise, `false` is pushed to stack.
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
    /// This instruction is particularly useful for efficiently implementing conditional OR.
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
    CallNative(Rc<NativeCallInfo>),
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
    /// Clones the value on the top of the stack and writes it to the local with the given index.
    PeekSave(usize),
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

impl Debug for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
            Instruction::PeekSave(local_idx) => f.write_fmt(format_args!("PSL, idx: {local_idx}")),
            Instruction::SaveGlobal(global_idx) => {
                f.write_fmt(format_args!("SGL, idx: {global_idx}"))
            }
            Instruction::Pop => f.write_str("POP"),
            Instruction::Throw(err) => f.write_fmt(format_args!("THW, {err}")),
            Instruction::Nop => f.write_str("NOP"),
        }
    }
}

struct InstructionsFormatter<'a> {
    sub_program: &'a SubProgram,
}

impl Debug for InstructionsFormatter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[ \n")?;
        for (idx, instruction) in self.sub_program.instructions.iter().enumerate() {
            f.write_fmt(format_args!("  {idx}: {instruction:?},\n"))?;
        }
        f.write_str("]")?;

        Ok(())
    }
}

//! Executes the generated bytecode.

use erl_parser::ast::BinaryOperator;

use crate::{
    bytecode::{Instruction, Module, SubProgram},
    err::RuntimeError,
    rcstr::RcStr,
    stdlib::{Type, Value},
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stack_new_should_fill_with_zeroed_ints() {
        for value in Stack::new().contents.iter() {
            assert_eq!(&Value::Integer(0), value);
        }
    }

    #[test]
    fn stack_push_should_assign_and_increment_ptr() {
        let mut stack = Stack::new();
        stack.push(Value::Integer(5));
        assert_eq!(Value::Integer(5), stack.contents[0]);
        assert_eq!(1, stack.top);
    }

    #[test]
    fn stack_pop_should_clone_and_decrement_ptr() {
        let mut stack = Stack::new();
        stack.contents[0] = Value::Integer(6);
        stack.top = 1;
        assert_eq!(Value::Integer(6), stack.pop());
        assert_eq!(0, stack.top);
    }

    #[test]
    fn stack_push_local_should_push_from_bottom_of_locals() {
        let mut stack = Stack::new();
        stack.contents[0] = Value::Integer(5); // This will act as our first local
        stack.top = 1;

        stack.push_local(0); // Push our first local to stack
        assert_eq!(Value::Integer(5), stack.contents[1]); // Should be pushed above the local
        assert_eq!(2, stack.top);
    }

    #[test]
    fn stack_push_global_should_push_from_bottom_of_stack() {
        let mut stack = Stack::new();
        stack.contents[0] = Value::Integer(5); // This will act as our first global

        stack.bottom_func = 1; // Set the bottom of our current function to above the global
        stack.top = 1;
        stack.push_global(0);

        // The global, which is not within our function, should be read instead of the first local
        assert_eq!(Value::Integer(5), stack.contents[1]);
        assert_eq!(2, stack.top);
    }

    #[test]
    fn stack_save_local_should_assign_to_bottom_of_locals() {
        let mut stack = Stack::new();
        // Assign an example value
        stack.contents[0] = Value::Integer(5);
        stack.contents[1] = Value::Integer(6); // Value that we are saving to the local
        stack.top = 2;

        stack.save_local(0);
        assert_eq!(Value::Integer(6), stack.contents[0]); // Local should be replaced with our variable
        assert_eq!(1, stack.top);
    }

    #[test]
    fn stack_save_global_should_assign_to_bottom_of_stack() {
        let mut stack = Stack::new();
        // Assign an example value
        stack.contents[0] = Value::Integer(5);
        stack.contents[1] = Value::Integer(6); // Value that we are saving to the local
        stack.top = 2;
        stack.bottom_func = 1; // Set the bottom of our current function to above the global

        stack.save_global(0);
        // Despite the global being below the bottom of the stack frame, it should still be assigned to
        assert_eq!(Value::Integer(6), stack.contents[0]);
        assert_eq!(1, stack.top);
    }

    #[test]
    fn stack_move_to_function_call_should_move_stack_frame() {
        let mut stack = Stack::new();

        stack.contents[0] = Value::Integer(5);
        stack.contents[1] = Value::Integer(7);
        stack.top = 2;

        // Moving to a function call should return the previous state of execution for pushing to the execution stack
        let old_exec_state = stack.move_to_function_call(3, 1);
        assert_eq!(1, old_exec_state.stack_frame_top);
        assert_eq!(0, old_exec_state.stack_frame_bottom);

        // Since we passed `1` for `arg_count`, the top value of the stack was assumed to be the argument.
        // This means that `bottom_func` should be `1`, since this argument is a local variable
        assert_eq!(1, stack.bottom_func);
        // We passed `3` for the total number of local variables.
        // This means that the stack pointer should be moved past the last local variable.
        assert_eq!(4, stack.top);
    }

    #[test]
    fn stack_move_to_caller_should_restore_stack_frame() {
        let exec_state = StackState {
            stack_frame_top: 10,
            stack_frame_bottom: 5,
        };
        let mut stack = Stack::new();
        stack.move_to_caller(exec_state);

        assert_eq!(10, stack.top);
        assert_eq!(5, stack.bottom_func);
    }

    #[test]
    fn stack_return_to_caller_should_push_result() {
        let mut stack = Stack::new();

        // Place a value at the top of the stack for returning
        stack.contents[9] = Value::Integer(10);
        stack.top = 10;

        // We are assuming that we called the function from the bottom of the stack
        let exec_state = StackState {
            stack_frame_top: 0,
            stack_frame_bottom: 0,
        };

        stack.return_to_caller(exec_state);

        // The return value should be pushed to the top of the stack
        assert_eq!(Value::Integer(10), stack.contents[0]);
        assert_eq!(1, stack.top);
    }
}

/// Stores the current state of the stack during paused execution of a function
struct StackState {
    /// The top of the stack frame
    stack_frame_top: usize,
    /// The bottom of the stack frame (where local variables start)
    stack_frame_bottom: usize,
}

/// Stores the currently executing instruction of a sub-program
struct InstructionState<'a> {
    /// The sub-program being executed
    sub_program: &'a SubProgram,
    /// The currently executing instruction
    instruction_ptr: usize,
}

impl<'a> InstructionState<'a> {
    /// Creates an [InstructionState], beginning execution at the start of the given [SubProgram].
    fn at_beginning_of(sub_program: &'a SubProgram) -> Self {
        Self {
            sub_program,
            instruction_ptr: 0,
        }
    }
}

/// Stores the state of execution of a sub-program whose execution has been paused,
/// due to a (non-native) sub-program call.
struct ExecState<'a> {
    /// The instruction to continue with when execution is resumed
    instruction: InstructionState<'a>,
    /// The stack state when execution was paused.
    stack: StackState,
}

/// The default stack, with a size of 8192 values.
pub(crate) type Stack = GenericStack<8192>;

/// A virtual stack for the interpreter.
pub(crate) struct GenericStack<const SIZE: usize> {
    /// The values within the stack.
    contents: [Value; SIZE],
    /// The stack index of the first local variable within the current sub-program
    bottom_func: usize,
    /// The stack index of the first value that is NOT part of the stack
    top: usize,
}

impl<const SIZE: usize> GenericStack<SIZE> {
    /// Creates a new stack with the given size.
    /// All values within the stack will be `Value::Integer(0)`.
    fn new() -> Self {
        let mut elements = Vec::new();
        for _ in 0..SIZE {
            elements.push(Value::Integer(0));
        }

        Self {
            contents: elements
                .try_into()
                .expect("Enough elements added to fill length"),
            bottom_func: 0,
            top: 0,
        }
    }

    /// Removes the value at the top of the stack, and returns it.
    #[inline(always)]
    pub(crate) fn pop(&mut self) -> Value {
        self.top -= 1;
        self.contents[self.top].clone()
    }

    /// Returns a clone of the top value of the stack, without removing it.
    #[inline(always)]
    pub fn peek(&self) -> Value {
        self.contents[self.top - 1].clone()
    }

    /// Pushes a value to the top of the stack.
    #[inline(always)]
    pub(crate) fn push(&mut self, value: Value) {
        self.contents[self.top] = value;
        self.top += 1;
    }

    /// Pushes the local with the given index to the top of the stack
    #[inline(always)]
    fn push_local(&mut self, idx: usize) {
        self.push(self.contents[self.bottom_func + idx as usize].clone());
    }

    /// Pushes the global with the given index (AKA the local of the main function with the given index) to the top the stack.
    #[inline(always)]
    fn push_global(&mut self, idx: usize) {
        self.push(self.contents[idx as usize].clone());
    }

    /// Pops the value at the top of the stack and saves it to the given local.
    #[inline(always)]
    fn save_local(&mut self, idx: usize) {
        self.contents[self.bottom_func + idx as usize] = self.pop();
    }

    /// Pops the value at the top of the stack and saves it to the given global.
    #[inline(always)]
    fn save_global(&mut self, idx: usize) {
        self.contents[idx as usize] = self.pop();
    }

    /// Moves the top and bottom of the current stack frame so that the bottom of the frame
    /// starts at the beginning of the arguments pushed by the caller, and the top of the frame
    /// points to the first position that is not within the local variables of the function.
    #[inline(always)]
    fn move_to_function_call(&mut self, local_count: usize, arg_count: usize) -> StackState {
        let at_start_of_args = self.top - arg_count as usize;

        let state = StackState {
            stack_frame_top: at_start_of_args,
            stack_frame_bottom: self.bottom_func,
        };

        self.bottom_func = at_start_of_args;
        self.top = self.bottom_func + local_count as usize;
        state
    }

    /// Moves to the given caller of the current function, assuming that there is no return value.
    #[inline(always)]
    fn move_to_caller(&mut self, exec_state: StackState) {
        self.bottom_func = exec_state.stack_frame_bottom;
        self.top = exec_state.stack_frame_top;
    }

    /// Moves to the given caller of the current function, pushing the return value to the stack.
    #[inline(always)]
    fn return_to_caller(&mut self, exec_state: StackState) {
        let return_value = self.pop();

        self.move_to_caller(exec_state);

        self.push(return_value);
    }
}

/// Executes the main sub-program within the given module
pub fn execute_main(module: &Module) -> Result<(), RuntimeError> {
    execute_idx(module, module.main_idx(), &[])?;

    Ok(())
}

/// Executes the sub program with the given name within the given module.
pub fn execute_by_name(
    module: &Module,
    name: &str,
    args: &[Value],
) -> Result<Option<Value>, RuntimeError> {
    for (idx, sub_program) in module.sub_programs.iter().enumerate() {
        if sub_program.name.as_deref() != Some(name) {
            continue;
        }

        // Check that the caller passed the right number of arguments
        if args.len() != sub_program.arg_count {
            return Err(RuntimeError::WrongNumberOfArguments {
                name: name.to_owned(),
                expected: sub_program.arg_count,
                actual: args.len(),
            });
        }

        return execute_idx(module, idx, args);
    }

    Err(RuntimeError::NoSuchSubProgram(name.to_owned()))
}

/// Executes the sub program with the given index within the given module.
fn execute_idx(
    module: &Module,
    sub_program_idx: usize,
    args: &[Value],
) -> Result<Option<Value>, RuntimeError> {
    // Create the stack which holds values being used by functions
    let mut stack = Stack::new();
    // Create the call stack
    let mut call_stack = Vec::new();

    // Move the stack pointer to after the locals of the main procedure (to make global variables available to other sub-programs
    // and to make local variables available to main)
    let main_proc = &module.sub_programs[module.main_idx()];
    stack.move_to_function_call(main_proc.local_count, 0);

    // Prepare the stack for the sub-program we're starting execution at, if it isn't main
    let entry_sub_program = &module.sub_programs[sub_program_idx];
    if entry_sub_program != main_proc {
        // Simulate a function call to the sub-program
        for arg in args {
            stack.push(arg.clone());
        }
        stack.move_to_function_call(entry_sub_program.local_count, entry_sub_program.arg_count);
    }

    // Start execution at the beginning of the given sub-program
    let mut state = InstructionState::at_beginning_of(entry_sub_program);
    loop {
        let instruction = match state
            .sub_program
            .instructions
            .get(state.instruction_ptr as usize)
        {
            Some(instruction) => instruction,
            None => &Instruction::Return, // If we are out of instructions, we will execute `Return` to move back up the call stack.
        };

        match instruction {
            // Very repetitive code for binary operations.
            // This code could be moved elsewhere, but I decided against it, since the functions wouldn't be used much elsewhere.
            Instruction::Add => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => {
                    stack.push(Value::Integer(left + right))
                }
                (Value::Integer(right), Value::Real(left)) => {
                    stack.push(Value::Real(left + right as f64))
                }
                (Value::Real(right), Value::Integer(left)) => {
                    stack.push(Value::Real(left as f64 + right))
                }
                (Value::Real(right), Value::Real(left)) => stack.push(Value::Real(left + right)),
                (Value::String(right), Value::String(left)) => {
                    stack.push(Value::String(RcStr::concat(&*left, &*right)))
                }
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Add)),
            },
            Instruction::Subtract => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => {
                    stack.push(Value::Integer(left - right))
                }
                (Value::Integer(right), Value::Real(left)) => {
                    stack.push(Value::Real(left - right as f64))
                }
                (Value::Real(right), Value::Integer(left)) => {
                    stack.push(Value::Real(left as f64 - right))
                }
                (Value::Real(right), Value::Real(left)) => stack.push(Value::Real(left - right)),
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Subtract)),
            },
            Instruction::Multiply => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => {
                    stack.push(Value::Integer(left * right))
                }
                (Value::Integer(right), Value::Real(left)) => {
                    stack.push(Value::Real(left * right as f64))
                }
                (Value::Real(right), Value::Integer(left)) => {
                    stack.push(Value::Real(left as f64 * right))
                }
                (Value::Real(right), Value::Real(left)) => stack.push(Value::Real(left * right)),
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Multiply)),
            },
            Instruction::Divide => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => {
                    stack.push(Value::Real(left as f64 / right as f64))
                }
                (Value::Integer(right), Value::Real(left)) => {
                    stack.push(Value::Real(left / right as f64))
                }
                (Value::Real(right), Value::Integer(left)) => {
                    stack.push(Value::Real(left as f64 / right))
                }
                (Value::Real(right), Value::Real(left)) => stack.push(Value::Real(left / right)),
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Divide)),
            },
            Instruction::Remainder => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => {
                    stack.push(Value::Integer(left % right))
                }
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Remainder)),
            },
            Instruction::Quotient => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => {
                    stack.push(Value::Integer(left / right))
                }
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Quotient)),
            },
            Instruction::Power => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => {
                    stack.push(Value::Integer(left.pow(right as u32)))
                }
                (Value::Integer(right), Value::Real(left)) => {
                    stack.push(Value::Real(left.powf(right as f64)))
                }
                (Value::Real(right), Value::Integer(left)) => {
                    stack.push(Value::Real((left as f64).powf(right)))
                }
                (Value::Real(right), Value::Real(left)) => {
                    stack.push(Value::Real(left.powf(right)))
                }
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Power)),
            },
            Instruction::GreaterThan => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => stack.push(if left > right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Integer(right), Value::Real(left)) => stack.push(if left > right as f64 {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Integer(left)) => stack.push(if left as f64 > right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Real(left)) => stack.push(if left > right {
                    Value::True
                } else {
                    Value::False
                }),
                _ => {
                    return Err(RuntimeError::CannotBinaryOperate(
                        BinaryOperator::GreaterThan,
                    ))
                }
            },
            Instruction::GreaterThanOrEquals => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => stack.push(if left >= right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Integer(right), Value::Real(left)) => stack.push(if left >= right as f64 {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Integer(left)) => stack.push(if left as f64 >= right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Real(left)) => stack.push(if left >= right {
                    Value::True
                } else {
                    Value::False
                }),
                _ => {
                    return Err(RuntimeError::CannotBinaryOperate(
                        BinaryOperator::GreaterThanOrEquals,
                    ))
                }
            },
            Instruction::LessThan => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => stack.push(if left < right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Integer(right), Value::Real(left)) => stack.push(if left < right as f64 {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Integer(left)) => {
                    stack.push(if (left as f64) < right as f64 {
                        Value::True
                    } else {
                        Value::False
                    })
                }
                (Value::Real(right), Value::Real(left)) => stack.push(if left < right {
                    Value::True
                } else {
                    Value::False
                }),
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::LessThan)),
            },
            Instruction::LessThanOrEquals => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => stack.push(if left <= right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Integer(right), Value::Real(left)) => stack.push(if left <= right as f64 {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Integer(left)) => {
                    stack.push(if (left as f64) <= right as f64 {
                        Value::True
                    } else {
                        Value::False
                    })
                }
                (Value::Real(right), Value::Real(left)) => stack.push(if left <= right {
                    Value::True
                } else {
                    Value::False
                }),
                _ => {
                    return Err(RuntimeError::CannotBinaryOperate(
                        BinaryOperator::LessThanOrEquals,
                    ))
                }
            },
            Instruction::Equals => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => stack.push(if left == right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Integer(right), Value::Real(left)) => stack.push(if left == right as f64 {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Integer(left)) => stack.push(if left as f64 == right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Real(left)) => stack.push(if left == right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::True, Value::True) => stack.push(Value::True),
                (Value::True, Value::False) => stack.push(Value::False),
                (Value::False, Value::True) => stack.push(Value::False),
                (Value::False, Value::False) => stack.push(Value::True),
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::Equals)),
            },
            Instruction::NotEquals => match (stack.pop(), stack.pop()) {
                (Value::Integer(right), Value::Integer(left)) => stack.push(if left != right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Integer(right), Value::Real(left)) => stack.push(if left != right as f64 {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Integer(left)) => stack.push(if left as f64 != right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::Real(right), Value::Real(left)) => stack.push(if left != right {
                    Value::True
                } else {
                    Value::False
                }),
                (Value::True, Value::True) => stack.push(Value::False),
                (Value::True, Value::False) => stack.push(Value::True),
                (Value::False, Value::True) => stack.push(Value::True),
                (Value::False, Value::False) => stack.push(Value::False),
                _ => return Err(RuntimeError::CannotBinaryOperate(BinaryOperator::NotEquals)),
            },
            Instruction::Not => match stack.pop() {
                Value::True => stack.push(Value::False),
                Value::False => stack.push(Value::True),
                _ => {
                    return Err(RuntimeError::WrongType {
                        expected: Type::Boolean,
                    })
                }
            },
            Instruction::JumpIfTrue(idx) => match stack.pop() {
                Value::True => {
                    state.instruction_ptr = *idx;
                    continue;
                }
                Value::False => {}
                _ => {
                    return Err(RuntimeError::WrongType {
                        expected: Type::Boolean,
                    })
                }
            },
            Instruction::JumpIfFalse(idx) => match stack.pop() {
                Value::True => {}
                Value::False => {
                    state.instruction_ptr = *idx;
                    continue;
                }
                _ => {
                    return Err(RuntimeError::WrongType {
                        expected: Type::Boolean,
                    })
                }
            },
            Instruction::JumpIfFalsePopIfTrue(idx) => match stack.peek() {
                Value::True => {
                    stack.pop();
                }
                Value::False => {
                    state.instruction_ptr = *idx;
                    continue;
                }
                _ => {
                    return Err(RuntimeError::WrongType {
                        expected: Type::Boolean,
                    })
                }
            },
            Instruction::JumpIfTruePopIfFalse(idx) => match stack.peek() {
                Value::True => {
                    state.instruction_ptr = *idx;
                    continue;
                }
                Value::False => {
                    stack.pop();
                }
                _ => {
                    return Err(RuntimeError::WrongType {
                        expected: Type::Boolean,
                    })
                }
            },
            Instruction::Jump(idx) => {
                state.instruction_ptr = *idx;
                continue;
            }
            Instruction::Call(func_idx) => {
                let to_call = &module.sub_programs[*func_idx as usize];
                let stack_state =
                    stack.move_to_function_call(to_call.local_count, to_call.arg_count);

                call_stack.push(ExecState {
                    instruction: state,
                    stack: stack_state,
                });
                state = InstructionState::at_beginning_of(to_call);
                continue;
            }
            Instruction::Return => {
                if state.sub_program.is_function {
                    return Err(RuntimeError::MustReturnValueFromFunction);
                }

                let caller_state = match call_stack.pop() {
                    Some(state) => state,
                    None => return Ok(None),
                };

                stack.move_to_caller(caller_state.stack);
                state = caller_state.instruction;
            }
            Instruction::ReturnValue => {
                if !state.sub_program.is_function {
                    return Err(RuntimeError::CannotReturnValueFromProcedure);
                }

                let caller_state = match call_stack.pop() {
                    Some(state) => state,
                    None => return Ok(Some(stack.pop())),
                };

                stack.return_to_caller(caller_state.stack);
                state = caller_state.instruction;
            }
            Instruction::LoadInteger(int) => stack.push(Value::Integer(*int)),
            Instruction::LoadReal(real) => stack.push(Value::Real(*real)),
            Instruction::LoadTrue => stack.push(Value::True),
            Instruction::LoadFalse => stack.push(Value::False),
            Instruction::LoadString(string) => stack.push(Value::String(string.clone())),
            Instruction::Load(local_idx) => stack.push_local(*local_idx),
            Instruction::LoadGlobal(global_idx) => stack.push_global(*global_idx),
            Instruction::Save(local_idx) => stack.save_local(*local_idx),
            Instruction::SaveGlobal(global_idx) => stack.save_global(*global_idx),
            Instruction::Pop => {
                stack.pop();
            }
            Instruction::Throw(err) => return Err((**err).clone()),
            Instruction::Nop => {}
            Instruction::CallNative(ptr) => ptr.0(&mut stack)?,
        };

        // Advance to the next instruction
        state.instruction_ptr += 1;
    }
}

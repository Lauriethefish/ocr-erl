//! Takes the AST and converts it into bytecode.
//!
//! This is not a particularly complicated process, since the AST maps quite
//! closely to the bytecode, due to the design of the bytecode format.
//!
//! Errors that can be detected while generating the bytecode (for example, calling a function that does not exist),
//! are stored within the bytecode to be thrown when they are reached by the executor. This is important
//! since, while this is a compiler, the executor is an interpreter, so we should display errors
//! only if they are actually reached.

use std::{cell::RefCell, collections::HashMap};

use crate::{
    bytecode::{Instruction, NativeCallInfo, SubProgram},
    err::RuntimeError,
    executor::Module,
    rcstr::RcStr,
    stdlib,
};

use erl_parser::ast::{
    Assignable, AssignmentValue, BinaryOperator, Call, Callee, Expression, IfSegment,
    RootStatement, Statement, UnaryOperator,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verify_global_context_new() {
        let sub_programs = RefCell::new(HashMap::new());

        let global_ctx = Context::new(None, &sub_programs, vec!["example".to_string()], false);

        assert!(global_ctx.global_function_context.is_none());
        assert_eq!(global_ctx.next_local_idx, 1);
        assert_eq!(global_ctx.locals.len(), 1);
        assert_eq!(
            global_ctx.locals.get("example"),
            Some(&Local {
                index: 0,
                is_const: false
            })
        );
        assert!(global_ctx.instructions.is_empty());
        assert_eq!(global_ctx.arg_count, 1);
        assert!(!global_ctx.is_function);
    }

    #[test]
    fn verify_context_new() {
        let sub_programs = RefCell::new(HashMap::new());

        let global_ctx = Context::new(None, &sub_programs, vec![], false);
        let ctx = Context::new(Some(global_ctx), &sub_programs, vec![], true);

        assert!(ctx.global_function_context.is_some());
        assert_eq!(ctx.next_local_idx, 0);
        assert!(ctx.locals.is_empty());
        assert!(ctx.instructions.is_empty());
        assert_eq!(ctx.arg_count, 0);
        assert!(ctx.is_function);
    }

    #[test]
    fn context_finish_should_return_correct_compiled_details() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec!["example".to_string()], true);
        ctx.next_local_idx += 1;
        ctx.instructions.push(Instruction::Nop);

        assert_eq!(
            SubProgram {
                local_count: 2,
                arg_count: 1,
                instructions: vec![Instruction::Nop],
                is_function: true,
                name: None
            },
            ctx.finish()
        )
    }

    #[test]
    fn context_emit_should_add_instruction() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);
        ctx.emit(Instruction::Nop);

        assert_eq!(vec![Instruction::Nop], ctx.instructions)
    }

    #[test]
    fn context_emit_should_return_correct_instruction_idx() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);
        assert_eq!(0, ctx.emit(Instruction::Nop));
        assert_eq!(1, ctx.emit(Instruction::Nop));
    }

    #[test]
    fn context_replace_should_replace_correct_instruction() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        ctx.instructions.push(Instruction::Nop);
        ctx.instructions.push(Instruction::Nop);

        ctx.replace(1, Instruction::Add);
        assert_eq!(ctx.instructions, vec![Instruction::Nop, Instruction::Add]);
    }

    #[test]
    fn context_insert_local_should_advance_local_idx() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        ctx.insert_local("example".to_string(), false);
        // Creating a local means that the next local should take up the next slot in the sub-program's locals array
        assert_eq!(1, ctx.next_local_idx)
    }

    #[test]
    fn context_insert_local_should_create_sequential_locals() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        ctx.insert_local("exampleVar".to_string(), false);
        ctx.insert_local("exampleConst".to_string(), true);

        // The locals index should move forward by one for each local
        assert_eq!(
            ctx.locals.get("exampleVar"),
            Some(&Local {
                index: 0,
                is_const: false
            })
        );
        assert_eq!(
            ctx.locals.get("exampleConst"),
            Some(&Local {
                index: 1,
                is_const: true
            })
        );
    }

    #[test]
    fn context_get_assignable_idx_should_fail_if_const_or_array_and_variable_exists() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        ctx.locals.insert(
            "example".to_string(),
            Local {
                is_const: false,
                index: 0,
            },
        );

        // Using the `const` or `array` keywords implies that a new variable is being declared
        // Thus, if the variable already exists, we should emit an error
        assert_eq!(
            ctx.get_assignable_idx("example".to_string(), false, true),
            Err(RuntimeError::CannotRedeclareVariable("example".to_string()))
        );
        assert_eq!(
            ctx.get_assignable_idx("example".to_string(), true, false),
            Err(RuntimeError::CannotRedeclareVariable("example".to_string()))
        );
    }

    #[test]
    fn context_get_assignable_idx_should_fail_if_variable_exists_and_is_constant() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        // The variable is a constant, so it cannot be assigned
        ctx.locals.insert(
            "example".to_string(),
            Local {
                is_const: true,
                index: 0,
            },
        );

        assert_eq!(
            ctx.get_assignable_idx("example".to_string(), false, false),
            Err(RuntimeError::CannotAssignConstant("example".to_string()))
        );
    }

    #[test]
    fn context_get_assignable_idx_should_succeed_if_non_const_variable_exists() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        // Create an existing variable which is NOT a constant
        ctx.locals.insert(
            "example".to_string(),
            Local {
                is_const: false,
                index: 5,
            },
        );
        // Its index should be returned, as it is assignable
        assert_eq!(
            ctx.get_assignable_idx("example".to_string(), false, false),
            Ok(5)
        );
    }

    #[test]
    fn context_get_assignable_idx_should_create_new_variable_if_variable_does_not_exist() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        // If a variable does not exist during the assignment, a new one should be declared and added to the config
        ctx.get_assignable_idx("example".to_string(), false, false)
            .unwrap();
        assert_eq!(
            ctx.locals.get("example"),
            Some(&Local {
                index: 0,
                is_const: false
            })
        );
    }

    #[test]
    fn context_save_should_emit_save_with_correct_variable() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        // Emit two saves to variables with the same name
        ctx.save("example".to_string(), false, false, false)
            .unwrap();
        ctx.save("example".to_string(), false, false, false)
            .unwrap();

        // Both instructions should save to 0, since we passed the same variable name
        assert_eq!(
            ctx.instructions,
            vec![Instruction::Save(0), Instruction::Save(0)]
        );
    }

    #[test]
    fn context_save_should_save_to_correct_existing_global() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut global_ctx = Context::new(None, &sub_programs, vec![], true);

        // Create an existing global variable which is NOT a constant
        global_ctx.locals.insert(
            "example".to_string(),
            Local {
                is_const: false,
                index: 5,
            },
        );

        let mut ctx = Context::new(Some(global_ctx), &sub_programs, vec![], true);
        ctx.save("example".to_string(), true, false, false).unwrap();

        // A `SaveGlobal` instruction should be used for globals
        assert_eq!(ctx.instructions, vec![Instruction::SaveGlobal(5)]);
    }

    #[test]
    fn context_save_should_deny_global_keyword_in_global_scope() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut global_ctx = Context::new(None, &sub_programs, vec![], true);

        // For now statements such as `global i = 2` in the global scope are currently not allowed
        // TODO: Should these be allowed in the future?
        assert_eq!(
            global_ctx.save("example".to_string(), true, false, false),
            Err(RuntimeError::CannotUseGlobalKeywordInGlobalScope)
        );
    }

    #[test]
    fn context_load_should_use_local_variable_if_exists() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        ctx.locals.insert(
            "example".to_string(),
            Local {
                is_const: false,
                index: 5,
            },
        );
        ctx.load("example".to_string()).unwrap();

        assert_eq!(ctx.instructions, vec![Instruction::Load(5)]);
    }

    #[test]
    fn context_load_should_use_global_variable_if_no_local() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut global_ctx = Context::new(None, &sub_programs, vec![], true);

        global_ctx.locals.insert(
            "example".to_string(),
            Local {
                is_const: false,
                index: 5,
            },
        );

        let mut ctx = Context::new(Some(global_ctx), &sub_programs, vec![], true);
        ctx.load("example".to_string()).unwrap();

        // `LoadGlobal` should be used instead of `Load`
        assert_eq!(ctx.instructions, vec![Instruction::LoadGlobal(5)]);
    }

    #[test]
    fn context_load_should_fail_if_no_local_or_global_variable() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut global_ctx = Context::new(None, &sub_programs, vec![], true);
        assert_eq!(
            global_ctx.load("example".to_string()),
            Err(RuntimeError::NoSuchVariable("example".to_string()))
        );

        let mut ctx = Context::new(Some(global_ctx), &sub_programs, vec![], true);
        assert_eq!(
            ctx.load("example".to_string()),
            Err(RuntimeError::NoSuchVariable("example".to_string()))
        );
    }

    #[test]
    fn context_throw_should_emit_err_instruction() {
        let sub_programs = RefCell::new(HashMap::new());
        let mut ctx = Context::new(None, &sub_programs, vec![], true);

        let err = RuntimeError::NoSuchVariable("example".to_string());
        ctx.emit_throw(err.clone());
        assert_eq!(ctx.instructions, vec![Instruction::Throw(Box::new(err))]);
    }
}

/// A local variable during compilation
#[derive(Copy, Clone, Debug, PartialEq)]
struct Local {
    /// `true` if the variable was declared as a constant.
    is_const: bool,
    /// The index of this local within the sub-program's locals array at runtime.
    index: usize,
}

/// The context for compiling a particular sub-program
struct Context<'a> {
    global_function_context: Option<Box<Context<'a>>>,
    available_sub_programs: &'a RefCell<HashMap<String, SubProgramCallInfo>>,

    next_local_idx: usize,
    locals: HashMap<String, Local>,

    instructions: Vec<Instruction>,

    arg_count: usize,
    is_function: bool,
}

#[derive(Copy, Clone)]
enum SubProgramType {
    Bytecode(usize),
    Native(&'static NativeCallInfo),
}

#[derive(Copy, Clone)]
struct SubProgramCallInfo {
    r#type: SubProgramType,
    arg_count: usize,
    is_function: bool,
}

/// Result type for emitting code.
/// This is returned by a compiler if an error is detected that prevents emitting further code.
/// Since we're creating an interpreter however, this will not trigger a compile time error, but instead will trigger an error instruction
/// to be appended to the block.
type Result<T> = std::result::Result<T, RuntimeError>;

impl<'a> Context<'a> {
    /// Creates the context for emitting a sub-program.
    pub fn new(
        global_function_context: Option<Context<'a>>,
        available_sub_programs: &'a RefCell<HashMap<String, SubProgramCallInfo>>,
        argument_names: Vec<String>,
        is_function: bool,
    ) -> Self {
        let mut result = Self {
            next_local_idx: 0,
            locals: HashMap::new(),
            arg_count: argument_names.len(),
            global_function_context: global_function_context.map(Box::new),
            available_sub_programs,
            is_function,
            instructions: Vec::new(),
        };

        for name in argument_names {
            result.insert_local(name, false);
        }

        result
    }

    /// Consumes this [Context], passing the emitted instructions and locals into a [SubProgram].
    pub fn finish(self) -> SubProgram {
        SubProgram {
            local_count: self.next_local_idx,
            arg_count: self.arg_count,
            instructions: self.instructions,
            is_function: self.is_function,
            name: None, // Set later in `compile_module`
        }
    }

    /// Emits the code for the given statement
    pub fn emit_next_statement(&mut self, statement: Statement) -> Result<()> {
        match statement {
            Statement::Call(call) => self.emit_call(call, false),
            Statement::Assign {
                is_const,
                is_global,
                is_array,
                to_assign,
                assign_with,
            } => self.emit_assignment(to_assign, assign_with, is_const, is_global, is_array),
            Statement::If {
                segments,
                else_block,
            } => self.emit_if(segments, else_block),
            Statement::While { condition, block } => self.emit_while(condition, block),
            Statement::For {
                start,
                end,
                step,
                variable_name,
                block,
            } => self.emit_for(start, end, step, variable_name, block),
            Statement::Return { value } => self.emit_return(value),
        }
    }

    pub fn emit_full_block(&mut self, block: Vec<Statement>) {
        for statement in block {
            match self.emit_next_statement(statement) {
                Ok(_) => {}
                Err(err) => {
                    self.emit_throw(err);
                    break;
                }
            }
        }
    }

    fn emit(&mut self, instruction: Instruction) -> usize {
        self.instructions.push(instruction);
        self.instructions.len() - 1
    }

    fn replace(&mut self, idx: usize, with: Instruction) {
        self.instructions[idx as usize] = with;
    }

    fn next_instruction_idx(&self) -> usize {
        self.instructions.len()
    }

    fn insert_local(&mut self, name: String, is_const: bool) -> usize {
        self.locals.insert(
            name,
            Local {
                index: self.next_local_idx,
                is_const,
            },
        );

        let result = self.next_local_idx;
        self.next_local_idx += 1;

        result
    }

    fn get_local(&mut self, name: &String) -> Option<Local> {
        self.locals.get(name).copied()
    }

    /// Gets the index of the given local for saving to, or creates a new variable if one does not exist.
    /// Existing variables are not allowed if either `is_const` or `is_array` are `true`, since this implies that the intent is to
    /// declare a new variable, not assign to an existing one.
    ///
    /// Verifies that the existing variable is not a constant.
    fn get_assignable_idx(
        &mut self,
        variable_name: String,
        is_const: bool,
        is_array: bool,
    ) -> Result<usize> {
        let must_be_new_declaration = is_const || is_array;

        match self.get_local(&variable_name) {
            Some(local) => {
                if must_be_new_declaration {
                    Err(RuntimeError::CannotRedeclareVariable(variable_name))
                } else if local.is_const {
                    Err(RuntimeError::CannotAssignConstant(variable_name))
                } else {
                    Ok(local.index)
                }
            }
            None => Ok(self.insert_local(variable_name, is_const)),
        }
    }

    /// Emits an instruction to save the value on the top of the stack to the given variable.
    fn save(
        &mut self,
        variable_name: String,
        is_global: bool,
        is_const: bool,
        is_array: bool,
    ) -> Result<()> {
        if is_global {
            let assignable = match &mut self.global_function_context {
                Some(ctx) => ctx.get_assignable_idx(variable_name, is_const, is_array)?,
                None => return Err(RuntimeError::CannotUseGlobalKeywordInGlobalScope),
            };

            self.emit(Instruction::SaveGlobal(assignable));
        } else {
            let assignable = self.get_assignable_idx(variable_name, is_const, is_array)?;
            self.emit(Instruction::Save(assignable));
        }

        Ok(())
    }

    /// Emits an instruction to load the given variable to the top of the stack
    fn load(&mut self, variable_name: String) -> Result<()> {
        match self.get_local(&variable_name) {
            Some(local) => self.emit(Instruction::Load(local.index)),
            None => match &mut self.global_function_context {
                Some(ctx) => match ctx.get_local(&variable_name) {
                    Some(global) => self.emit(Instruction::LoadGlobal(global.index)),
                    None => return Err(RuntimeError::NoSuchVariable(variable_name)),
                },
                None => return Err(RuntimeError::NoSuchVariable(variable_name)),
            },
        };
        Ok(())
    }

    fn emit_if(
        &mut self,
        segments: Vec<IfSegment>,
        else_block: Option<Vec<Statement>>,
    ) -> Result<()> {
        let mut replace_with_jump_out = Vec::new();

        let last_segment_idx = segments.len() - 1;
        for (idx, segment) in segments.into_iter().enumerate() {
            self.emit_expression(segment.condition)?;
            let pending_jump_idx = self.emit(Instruction::Nop);
            self.emit_full_block(segment.block);

            self.replace(
                pending_jump_idx,
                Instruction::JumpIfFalse(self.next_instruction_idx()),
            );

            // If this segment is not the last segment, or there is an else block, we need to insert
            // a jump out of the `if` statement at this point, to avoid executing the subsequent segments.
            if idx != last_segment_idx || else_block.is_some() {
                replace_with_jump_out.push(self.emit(Instruction::Nop));
            }
        }

        if let Some(else_block) = else_block {
            self.emit_full_block(else_block);
        }

        for idx in replace_with_jump_out {
            self.replace(idx, Instruction::Jump(self.next_instruction_idx()));
        }

        Ok(())
    }

    fn emit_for(
        &mut self,
        start: Expression,
        end: Expression,
        step: Option<Expression>,
        variable_name: String,
        block: Vec<Statement>,
    ) -> Result<()> {
        self.emit_expression(start)?;
        self.save(variable_name.clone(), false, false, false)?;

        let step_expr = match step {
            Some(expr) => expr,
            None => Expression::IntegerLiteral(1),
        };

        let insert_jump_to_condition_idx = self.emit(Instruction::Nop);
        let start_of_block_idx = self.next_instruction_idx();
        self.emit_full_block(block);

        self.load(variable_name.clone())?;
        self.emit_expression(step_expr)?;
        self.emit(Instruction::Add);
        self.save(variable_name.clone(), false, false, false)?;

        self.replace(
            insert_jump_to_condition_idx,
            Instruction::Jump(self.next_instruction_idx()),
        );
        self.load(variable_name)?;
        self.emit_expression(end)?;
        self.emit(Instruction::LessThanOrEquals);
        self.emit(Instruction::JumpIfTrue(start_of_block_idx));

        Ok(())
    }

    fn emit_while(&mut self, condition: Expression, block: Vec<Statement>) -> Result<()> {
        let insert_jump_to_condition = self.emit(Instruction::Nop);
        let start_of_block_idx = self.next_instruction_idx();
        self.emit_full_block(block);
        self.replace(
            insert_jump_to_condition,
            Instruction::Jump(self.next_instruction_idx()),
        );
        self.emit_expression(condition)?;
        self.emit(Instruction::JumpIfTrue(start_of_block_idx));

        Ok(())
    }

    fn emit_return(&mut self, value: Option<Expression>) -> Result<()> {
        match value {
            Some(expr) => {
                self.emit_expression(expr)?;
                self.emit(Instruction::ReturnValue)
            }
            None => self.emit(Instruction::Return),
        };
        Ok(())
    }

    fn emit_assignment(
        &mut self,
        to_assign: Assignable,
        assign_with: AssignmentValue,
        is_global: bool,
        is_const: bool,
        is_array: bool,
    ) -> Result<()> {
        match assign_with {
            AssignmentValue::Expression(expr) => self.emit_expression(expr)?,
            AssignmentValue::BlankArray(_) => todo!(), // TODO: Need an instruction for creating arrays
        }

        match to_assign {
            Assignable::Index {
                to_index: _,
                indices: _,
            } => todo!(), // TODO: Need an instruction for indexing arrays
            Assignable::Property { value: _, name: _ } => todo!(), // TODO: Need an instruction for getting properties
            Assignable::Variable(name) => self.save(name, is_global, is_const, is_array),
        }
    }

    fn emit_call(&mut self, call: Call, using_return_value: bool) -> Result<()> {
        let name = match *call.callee {
            Callee::Member {
                object: _,
                member: _,
            } => todo!(),
            Callee::SubProgram(name) => name,
        };

        let sub_programs = self.available_sub_programs.borrow();
        let call_info = match sub_programs.get(&name) {
            Some(sub_program) => sub_program,
            None => return Err(RuntimeError::NoSuchSubProgram(name)),
        };

        // If the return value of this sub-program needs to be used in an expression, then we will return Err for procedures
        // (as they return no value)
        if using_return_value && !call_info.is_function {
            return Err(RuntimeError::CannotUseProcedureInExpression(name));
        }

        // Make sure that the right number is arguments is being passed
        if call_info.arg_count != call.args.len() {
            return Err(RuntimeError::WrongNumberOfArguments {
                name,
                expected: call_info.arg_count,
                actual: call.args.len(),
            });
        }

        // Push the arguments to the stack, one at a time
        for arg in call.args {
            self.emit_expression(arg)?;
        }

        self.emit(match call_info.r#type {
            SubProgramType::Bytecode(idx) => Instruction::Call(idx),
            SubProgramType::Native(ptr) => Instruction::CallNative(ptr),
        });

        // If we do not need the return value of this function (e.g. in a statement), then we should pop it off of the stack
        if !using_return_value && call_info.is_function {
            self.emit(Instruction::Pop);
        }

        Ok(())
    }

    fn emit_expression(&mut self, expression: Expression) -> Result<()> {
        match expression {
            Expression::StringLiteral(string) => {
                self.emit(Instruction::LoadString(RcStr::new(&string)));
            }
            Expression::IntegerLiteral(int) => {
                self.emit(Instruction::LoadInteger(int));
            }
            Expression::RealLiteral(real) => {
                self.emit(Instruction::LoadReal(real));
            }
            Expression::BooleanLiteral(value) => {
                if value {
                    self.emit(Instruction::LoadTrue);
                } else {
                    self.emit(Instruction::LoadFalse);
                }
            }
            Expression::ArrayLiteral(_) => todo!(),
            Expression::Assignable(expr) => match expr {
                Assignable::Index {
                    to_index: _,
                    indices: _,
                } => todo!(), // TODO: Need a function for indexing arrays
                Assignable::Property { value: _, name: _ } => todo!(), // TODO: Need a function for getting properties
                Assignable::Variable(name) => {
                    self.load(name)?;
                }
            },
            Expression::Call(call) => self.emit_call(call, true)?,
            Expression::Binary {
                operator,
                left,
                right,
            } => self.emit_binary_expression(operator, *left, *right)?,
            Expression::Unary { operand, operator } => {
                self.emit_unary_expression(operator, *operand)?
            }
        };
        Ok(())
    }

    fn emit_unary_expression(
        &mut self,
        operator: UnaryOperator,
        operand: Expression,
    ) -> Result<()> {
        self.emit_expression(operand)?;
        self.emit(match operator {
            UnaryOperator::Not => Instruction::Not,
        });
        Ok(())
    }

    fn emit_binary_expression(
        &mut self,
        operator: BinaryOperator,
        left: Expression,
        right: Expression,
    ) -> Result<()> {
        match operator {
            BinaryOperator::Add => self.emit_simple_bin_expr(Instruction::Add, left, right),
            BinaryOperator::Subtract => {
                self.emit_simple_bin_expr(Instruction::Subtract, left, right)
            }
            BinaryOperator::Multiply => {
                self.emit_simple_bin_expr(Instruction::Multiply, left, right)
            }
            BinaryOperator::Divide => self.emit_simple_bin_expr(Instruction::Divide, left, right),
            BinaryOperator::Power => self.emit_simple_bin_expr(Instruction::Power, left, right),
            BinaryOperator::Remainder => {
                self.emit_simple_bin_expr(Instruction::Remainder, left, right)
            }
            BinaryOperator::Quotient => {
                self.emit_simple_bin_expr(Instruction::Quotient, left, right)
            }
            BinaryOperator::Equals => self.emit_simple_bin_expr(Instruction::Equals, left, right),
            BinaryOperator::NotEquals => {
                self.emit_simple_bin_expr(Instruction::NotEquals, left, right)
            }
            BinaryOperator::GreaterThan => {
                self.emit_simple_bin_expr(Instruction::GreaterThan, left, right)
            }
            BinaryOperator::GreaterThanOrEquals => {
                self.emit_simple_bin_expr(Instruction::GreaterThanOrEquals, left, right)
            }
            BinaryOperator::LessThan => {
                self.emit_simple_bin_expr(Instruction::LessThan, left, right)
            }
            BinaryOperator::LessThanOrEquals => {
                self.emit_simple_bin_expr(Instruction::LessThanOrEquals, left, right)
            }
            BinaryOperator::And => {
                // AND conditional expressions work slightly differently to what you would expect
                // If the left value is false, then we can skip evaluating the right-hand side since we already know it to be true
                self.emit_expression(left)?;
                let replace_with_jump = self.emit(Instruction::Nop);
                self.emit_expression(right)?;

                self.replace(
                    replace_with_jump,
                    Instruction::JumpIfFalsePopIfTrue(self.next_instruction_idx()),
                );
                Ok(())
            }
            BinaryOperator::Or => {
                // For OR conditional expressions, if the left value is true, we can skip evaluating the right-hand side since we
                // already know that the result will be true.
                self.emit_expression(left)?;
                let replace_with_jump = self.emit(Instruction::Nop);
                self.emit_expression(right)?;

                self.replace(
                    replace_with_jump,
                    Instruction::JumpIfTruePopIfFalse(self.next_instruction_idx()),
                );
                Ok(())
            }
        }
    }

    fn emit_simple_bin_expr(
        &mut self,
        action: Instruction,
        left: Expression,
        right: Expression,
    ) -> Result<()> {
        self.emit_expression(left)?;
        self.emit_expression(right)?;
        self.emit(action);
        Ok(())
    }

    /// Emits an instruction to throw the given error.
    fn emit_throw(&mut self, error: RuntimeError) {
        self.emit(Instruction::Throw(Box::new(error)));
    }
}

/// Compiles the given AST into the ERL bytecode
pub fn compile(program: Vec<RootStatement>) -> Module {
    let sub_programs_by_name = RefCell::new(HashMap::new());

    for (name, sub_program) in stdlib::BUILT_IN_SUB_PROGRAMS.into_iter() {
        sub_programs_by_name.borrow_mut().insert(
            name.to_string(),
            SubProgramCallInfo {
                r#type: SubProgramType::Native(sub_program),
                arg_count: sub_program.arg_count,
                is_function: sub_program.is_function,
            },
        );
    }

    let mut sub_programs: Vec<SubProgram> = Vec::new();
    let mut global_ctx = Context::new(None, &sub_programs_by_name, Vec::new(), false);

    for statement in program {
        match statement {
            RootStatement::Statement(statement) => {
                match global_ctx.emit_next_statement(statement) {
                    Ok(_) => {}
                    Err(err) => {
                        global_ctx.emit_throw(err);
                        break;
                    }
                }
            }
            RootStatement::SubProgram {
                name,
                block,
                argument_names,
                is_function,
            } => {
                // To allow recursion, we will first construct the `SubProgramCallInfo` for this sub-program.
                let idx = sub_programs.len();
                let call_info = SubProgramCallInfo {
                    r#type: SubProgramType::Bytecode(idx),
                    arg_count: argument_names.len(),
                    is_function,
                };

                // ...and insert it into the map of available sub-programs before compiling
                let mut sub_program_map = sub_programs_by_name.borrow_mut();
                if sub_program_map.contains_key(&name) {
                    global_ctx.emit_throw(RuntimeError::DuplicateSubProgramName(name));
                    break;
                }
                sub_program_map.insert(name.clone(), call_info);
                drop(sub_program_map); // Drop the borrow to allow the sub-programs map to be accessed by the compiler.

                let mut ctx = Context::new(
                    Some(global_ctx),
                    &sub_programs_by_name,
                    argument_names,
                    is_function,
                );
                ctx.emit_full_block(block);
                global_ctx = *ctx
                    .global_function_context
                    .take()
                    .expect("Global context must exist as it was passed in above");
                let mut sub_program = ctx.finish();

                sub_program.name = Some(name.clone());
                sub_programs.push(sub_program);
            }
        }
    }
    sub_programs.push(global_ctx.finish());

    let main_idx = sub_programs.len() - 1;
    Module::new(sub_programs, main_idx)
}

use std::mem::MaybeUninit;

use crate::{err::RuntimeError, stdlib::Value};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stack_new_should_create_with_correct_size() {
        let stack = Stack::new(10);

        assert_eq!(10, stack.contents.len());
        assert_eq!(0, stack.first_local_idx); // This can be equal to `size`, since `size` is 0.
        assert_eq!(0, stack.end_locals_idx);
        assert_eq!(0, stack.size);
    }

    #[test]
    fn stack_push_should_increment_stack_size_and_assign_to_contents() {
        let mut stack = Stack::new(10);
        stack.push(Value::Integer(5)).unwrap();

        assert_eq!(1, stack.size);
        assert_eq!(Value::Integer(5), unsafe {
            stack.contents[0].assume_init_read()
        });
    }

    #[test]
    fn stack_push_should_return_err_if_stack_full() {
        let mut stack = Stack::new(2);
        stack.push(Value::Integer(5)).unwrap();
        stack.push(Value::Integer(5)).unwrap();
        assert_eq!(
            Err(RuntimeError::StackOverflow),
            stack.push(Value::Integer(5))
        );
    }

    #[test]
    fn stack_push_unchecked_should_increment_stack_size_and_assign_to_contents() {
        let mut stack = Stack::new(10);
        unsafe { stack.push_unchecked(Value::Integer(5)) };

        assert_eq!(1, stack.size);
        assert_eq!(Value::Integer(5), unsafe {
            stack.contents[0].assume_init_read()
        });
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Called `push_unchecked` with full stack")]
    fn stack_push_unchecked_should_dbg_assert_stack_not_full() {
        let mut stack = Stack::new(2);
        stack.push(Value::Integer(5)).unwrap();
        stack.push(Value::Integer(5)).unwrap();

        unsafe { stack.push_unchecked(Value::Integer(5)) };
    }

    #[test]
    fn stack_pop_should_decrement_ptr_and_return_top_value() {
        let mut stack = Stack::new(10);
        stack.push(Value::Integer(5)).unwrap();

        let value = stack.pop();
        assert_eq!(0, stack.size);
        assert_eq!(Value::Integer(5), value);
    }

    #[test]
    #[should_panic(expected = "Attempted to `pop` when stack size was 0")]
    fn stack_pop_should_panic_if_stack_empty() {
        let mut stack = Stack::new(10);
        stack.pop();
    }

    #[test]
    #[should_panic(expected = "Attempted to `pop` local variable from stack")]
    fn stack_pop_should_panic_if_popping_local() {
        let mut stack = Stack::new(10);

        // Simulate a local variable at index 0 on the stack
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.first_local_idx = 0;
        stack.end_locals_idx = 1;
        stack.size = 1;

        stack.pop();
    }

    #[test]
    fn stack_pop_unchecked_should_decrement_ptr_and_return_top_value() {
        let mut stack = Stack::new(10);
        stack.push(Value::Integer(5)).unwrap();

        let value = unsafe { stack.pop_unchecked() };
        assert_eq!(0, stack.size);
        assert_eq!(Value::Integer(5), value);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Called `pop_unchecked` with empty stack")]
    fn stack_pop_unchecked_should_dbg_assert_stack_not_empty() {
        let mut stack = Stack::new(10);
        unsafe { stack.pop_unchecked() };
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "Attempted to `pop_unchecked` a local variable")]
    fn stack_pop_unchecked_should_dbg_assert_not_popping_local() {
        let mut stack = Stack::new(10);

        // Simulate a local variable at index 0 on the stack
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.first_local_idx = 0;
        stack.end_locals_idx = 1;
        stack.size = 1;

        unsafe { stack.pop_unchecked() };
    }

    #[test]
    fn stack_push_local_should_increment_ptr_and_assign_to_contents() {
        let mut stack = Stack::new(10);

        // Simulate a local variable at index 0 on the stack
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.first_local_idx = 0;
        stack.end_locals_idx = 1;
        stack.size = 1;

        stack.push_local(0).unwrap();

        assert_eq!(Value::Integer(5), unsafe {
            stack.contents[0].assume_init_read()
        });
        assert_eq!(2, stack.size);
    }

    #[test]
    #[should_panic(
        expected = "Attempted to read from a local outside the range of the locals within the stack frame"
    )]
    fn stack_push_local_should_panic_if_local_out_of_range() {
        let mut stack = Stack::new(10);

        stack.push_local(0).unwrap();
    }

    #[test]
    fn stack_push_local_unchecked_should_increment_ptr_and_assign_to_contents() {
        let mut stack = Stack::new(10);

        // Simulate a local variable at index 0 on the stack
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.first_local_idx = 0;
        stack.end_locals_idx = 1;
        stack.size = 1;

        unsafe { stack.push_local_unchecked(0) };

        assert_eq!(Value::Integer(5), unsafe {
            stack.contents[0].assume_init_read()
        });
        assert_eq!(2, stack.size);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(
        expected = "Attempted to read from a local outside the range of the locals within the stack frame"
    )]
    fn stack_push_local_should_dbg_assert_local_within_range() {
        let mut stack = Stack::new(10);

        unsafe { stack.push_local_unchecked(0) };
    }

    #[test]
    fn stack_save_to_local_should_decrement_ptr_and_write_to_local() {
        let mut stack = Stack::new(10);

        // Simulate a local variable at index 0 on the stack
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.first_local_idx = 0;
        stack.end_locals_idx = 1;
        stack.size = 1;

        stack.contents[1] = MaybeUninit::new(Value::Integer(6));
        stack.size = 2;

        stack.save_to_local(0);

        // The stack size should be decremented, as save_to_local pops from the top of the stack
        assert_eq!(1, stack.size);
        // The value at the tpo of the stack should be saved to the local
        assert_eq!(Value::Integer(6), unsafe {
            stack.contents[0].assume_init_read()
        })
    }

    #[test]
    #[should_panic(
        expected = "Attempted to write to a local outside the range of the locals within the stack frame"
    )]
    fn stack_save_to_local_should_panic_if_local_out_of_range() {
        let mut stack = Stack::new(10);
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.size = 1;

        stack.save_to_local(0);
    }

    #[test]
    fn stack_save_to_local_unchecked_should_decrement_ptr_and_write_to_local() {
        let mut stack = Stack::new(10);

        // Simulate a local variable at index 0 on the stack
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.first_local_idx = 0;
        stack.end_locals_idx = 1;
        stack.size = 1;

        stack.contents[1] = MaybeUninit::new(Value::Integer(6));
        stack.size = 2;

        unsafe { stack.save_to_local_unchecked(0) };

        // The stack size should be decremented, as save_to_local pops from the top of the stack
        assert_eq!(1, stack.size);
        // The value at the tpo of the stack should be saved to the local
        assert_eq!(Value::Integer(6), unsafe {
            stack.contents[0].assume_init_read()
        })
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(
        expected = "Attempted to write to a local outside the range of the locals within the stack frame"
    )]
    fn stack_save_to_local_unchecked_should_dbg_assert_local_within_range() {
        let mut stack = Stack::new(10);
        stack.contents[0] = MaybeUninit::new(Value::Integer(5));
        stack.size = 1;

        unsafe {
            stack.save_to_local_unchecked(0);
        }
    }

    #[test]
    fn stack_begin_new_stack_frame_should_succeed_if_enough_space() {
        let mut stack = Stack::new(10);

        // Push an example argument
        stack.push(Value::Integer(10)).unwrap();
        assert_eq!(
            // The returned stack frame should match that before execution, but with the argument popped from stack
            Ok(StackFrame {
                size: 0,
                first_local_idx: 0,
                end_locals_idx: 0
            }),
            // Begin a new stack frame with one argument and one local (which is that argument)
            //
            // 10 is passed as the maximum stack space, since this is the maximum space available from the beginning
            // of the locals of the new frame (from the start of the stack in this case)
            stack.begin_new_stack_frame(1, 1, 10)
        );

        // The stack should not be modified by a funciton call
        assert_eq!(1, stack.size);
        // The first element in the stack (our argument), is now a valid local
        assert_eq!(0, stack.first_local_idx);
        assert_eq!(1, stack.end_locals_idx);
    }

    #[test]
    fn stack_begin_new_stack_frame_should_initialise_local_variables() {
        let mut stack = Stack::new(10);
        // Push an example argument
        stack.push(Value::Integer(6)).unwrap();

        // `local_count` is 2 higher than `arg_count`, so two extra local variables should be pushed to stack
        stack.begin_new_stack_frame(1, 3, 3).unwrap();

        // Our argument should remain untouched.
        assert_eq!(Value::Integer(6), unsafe {
            stack.contents[0].assume_init_read()
        });
        // The two local variables should be initialised to zero
        for i in 1..=2 {
            assert_eq!(Value::Integer(0), unsafe {
                stack.contents[i].assume_init_read()
            })
        }

        assert_eq!(3, stack.size); // Our 1 argument + the 2 non-argument locals
        assert_eq!(0, stack.first_local_idx); // First local (the argument), is at the bottom of the stack, idx 0
        assert_eq!(3, stack.end_locals_idx); // Last local is at idx 2, so end_locals_idx is 3.
    }

    #[test]
    fn stack_begin_new_stack_frame_should_return_err_if_insuffient_space() {
        let mut stack = Stack::new(10);
        assert_eq!(
            Err(RuntimeError::StackOverflow),
            stack.begin_new_stack_frame(0, 0, 11)
        );
    }

    #[test]
    #[should_panic(expected = "Cannot have more arguments than local variables")]
    fn stack_begin_new_stack_frame_should_panic_if_more_args_than_locals() {
        let mut stack = Stack::new(10);
        stack.begin_new_stack_frame(2, 1, 3).unwrap();
    }

    #[test]
    #[should_panic(expected = "Not enough arguments pushed to stack for stack frame")]
    fn stack_begin_new_stack_frame_should_panic_if_insufficient_args_pushed() {
        let mut stack = Stack::new(10);
        stack.push(Value::Integer(3)).unwrap();
        stack.begin_new_stack_frame(2, 2, 2).unwrap();
    }

    #[test]
    #[should_panic(expected = "Stack frame must require at least `local_count` max space")]
    fn stack_begin_new_stack_frame_should_panic_if_insufficient_space_accounted_for_locals() {
        let mut stack = Stack::new(10);
        stack.begin_new_stack_frame(0, 2, 1).unwrap();
    }

    #[test]
    fn stack_return_to_frame_should_restore_correct_frame() {
        let mut stack = Stack::new(10);
        // Simulate two local variables in the function being returned from
        stack.push(Value::Integer(5)).unwrap();
        stack.push(Value::Integer(6)).unwrap();
        stack.first_local_idx = 0;
        stack.end_locals_idx = 2;

        let return_to = StackFrame {
            // Since we are returning to size 0, these two locals should be popped
            size: 0,
            first_local_idx: 0,
            end_locals_idx: 0,
        };

        stack.return_to_frame(return_to);
        // Verify that the frame is correctly aligned
        assert_eq!(0, stack.size);
        assert_eq!(0, stack.first_local_idx);
        assert_eq!(0, stack.end_locals_idx);
    }

    #[test]
    #[should_panic(expected = "Cannot pop back to stack frame that is above this one")]
    fn stack_return_to_frame_should_panic_if_frame_above_current_size() {
        let mut stack = Stack::new(10);
        let invalid_frame = StackFrame {
            size: 5,
            first_local_idx: 3,
            end_locals_idx: 4,
        };

        stack.return_to_frame(invalid_frame);
    }

    #[test]
    fn stack_return_value_to_frame_should_push_return_value() {
        let mut stack = Stack::new(10);
        // Simulate two local variables in the function being returned from
        stack.push(Value::Integer(5)).unwrap();
        stack.push(Value::Integer(6)).unwrap();
        stack.first_local_idx = 0;
        stack.end_locals_idx = 2;

        // This value should be returned from the frame
        stack.push(Value::Integer(7)).unwrap();

        let return_to = StackFrame {
            // Since we are returning to size 0, these two locals should be popped
            size: 0,
            first_local_idx: 0,
            end_locals_idx: 0,
        };

        stack.return_value_to_frame(return_to);
        // The return value should be pushed to the calling function
        assert_eq!(Value::Integer(7), unsafe {
            stack.contents[0].assume_init_read()
        });
        assert_eq!(1, stack.size);

        // Other details of the stack frame should match
        assert_eq!(0, stack.first_local_idx);
        assert_eq!(0, stack.end_locals_idx);
    }
}

/// Stores a captured state of the stack
#[derive(Debug, PartialEq)]
pub struct StackFrame {
    size: usize,
    first_local_idx: usize,
    end_locals_idx: usize,
}

pub(crate) struct Stack {
    /// The values within the stack.
    contents: Box<[MaybeUninit<Value>]>,
    /// The stack index of the first value that is NOT part of the stack.
    /// The index of `size` may be out of bounds of `contents` by one element ONLY if the stack is full.
    /// If the stack is not empty, all values from index `size - 1` down to 0 must ALWAYS be initialised stack elements.
    size: usize,
    /// The index of the first local variable within the current sub-program. Must be below `size` unless `end_locals_idx`
    /// is equal to `size`.
    first_local_idx: usize,
    /// The first index on the stack that is NOT a local variable. Must be less than or equal to `size`.
    end_locals_idx: usize,
}

impl Stack {
    /// Creates a new [Stack] with the given size.
    ///
    /// # Arguments
    /// * `size` - the maximum number of elements.
    pub fn new(size: usize) -> Self {
        let mut contents = Vec::new();
        contents.reserve_exact(size);

        for _ in 0..size {
            contents.push(MaybeUninit::uninit());
        }

        Self {
            contents: contents.into(),
            size: 0,
            first_local_idx: 0,
            end_locals_idx: 0,
        }
    }

    /// Pushes the given value to the top of the stack.
    /// Returns `Ok` if the stack is not full, or `Err` with [`RuntimeError::StackOverflow`] if the stack is full.
    #[inline]
    pub fn push(&mut self, value: Value) -> Result<(), RuntimeError> {
        match self.contents.get_mut(self.size) {
            Some(uninit) => {
                uninit.write(value);
                self.size += 1;

                Ok(())
            }
            None => Err(RuntimeError::StackOverflow),
        }
    }

    /// Pushes the given value to the top of the stack.
    ///
    /// # Safety
    /// Calling this function is undefined behaviour if the stack is full.
    #[inline]
    pub unsafe fn push_unchecked(&mut self, value: Value) {
        // SAFETY: It is up to the caller to uphold that the stack is NOT full before calling this function.
        // If the stack is not full, then `self.size` must point to a valid element within `contents`.
        debug_assert!(
            self.size < self.contents.len(),
            "Called `push_unchecked` with full stack"
        );
        unsafe { self.contents.get_unchecked_mut(self.size) }.write(value);
        self.size += 1;
    }

    /// Removes the value at the top of the stack and returns it.
    ///
    /// # Panics
    /// Panics if the stack is empty, or if attempting to pop a local variable from the stack.
    #[inline]
    pub fn pop(&mut self) -> Value {
        assert!(self.size > 0, "Attempted to `pop` when stack size was 0");
        assert!(
            self.size > self.end_locals_idx,
            "Attempted to `pop` local variable from stack"
        );

        self.size -= 1;
        unsafe {
            // SAFETY: `self.size - 1` must always point to an inbounds, initialised element within the stack if the stack is not empty.
            // Thus, since we just subtracted one from `self.size` above, and used checked subtraction to make sure that `self.size` wasn't
            // zero, the stack must not be empty and `self.size - 1` is inbounds and initialised.
            //
            // Additionally, using `assume_init_read` is safe since the value at `self.size` is no longer within the stack after this call,
            // and thus will never be read.
            self.contents.get_unchecked(self.size).assume_init_read()
        }
    }

    /// Removes the value at the top of the stack and returns it.
    ///
    /// # Safety
    /// If calling [`Stack::pop`] would panic, calling this function is undefined bebaviour.
    #[inline]
    pub unsafe fn pop_unchecked(&mut self) -> Value {
        debug_assert!(self.size != 0, "Called `pop_unchecked` with empty stack");
        debug_assert!(
            self.size > self.end_locals_idx,
            "Attempted to `pop_unchecked` a local variable"
        );

        self.size -= 1;
        unsafe {
            // SAFETY: `self.size - 1` must always point to an inbounds, initialised element within the stack if the stack is not empty.
            // The caller must uphold that the stack is not empty, thus `self.size - 1` is inbounds and initialised.
            //
            // Additionally, using `assume_init_read` is safe since the value at `self.size` is no longer within the stack after this call,
            // and thus will never be read.
            self.contents.get_unchecked(self.size).assume_init_read()
        }
    }

    /// Pushes the value of a local variable within the current stack frame.
    ///
    /// # Panics
    /// This function will panic if `idx` is greater than or equal to the `local_count` passed to
    /// the last call to [`Stack::begin_stack_frame()`].
    #[inline]
    pub fn push_local(&mut self, idx: usize) -> Result<(), RuntimeError> {
        let local_idx = self.first_local_idx + idx;
        assert!(
            local_idx < self.end_locals_idx,
            "Attempted to read from a local outside the range of the locals within the stack frame"
        );

        // SAFETY: If the local is within the locals of the last call to `begin_stack_frame`, `local_idx` must be less
        // than `self.size`, and thus it is an initialised value within the bounds of contents.
        let local = unsafe {
            self.contents
                .get_unchecked(local_idx)
                .assume_init_ref()
                .clone()
        };

        self.push(local)
    }

    /// Pushes the value of a local variable within the current stack frame.
    ///
    /// # Safety
    /// The result is undefined behaviour if:
    /// * The stack is full.
    /// * `idx` is greater than or equal to the `local_count` passed to
    /// the last call to [`Stack::begin_stack_frame()`]
    #[inline]
    pub unsafe fn push_local_unchecked(&mut self, idx: usize) {
        let local_idx = self.first_local_idx + idx;
        debug_assert!(
            local_idx < self.end_locals_idx,
            "Attempted to read from a local outside the range of the locals within the stack frame"
        );

        // SAFETY: If the local is within the locals of the last call to `begin_stack_frame` (as verified by the caller),
        // then `local_idx` must be less than `self.size`, and thus it is an initialised value within the bounds of `contents`.
        let local = unsafe {
            self.contents
                .get_unchecked(local_idx)
                .assume_init_ref()
                .clone()
        };

        // SAFETY: It is up to the caller to ensure that the stack is not full.
        unsafe { self.push_unchecked(local) };
    }

    /// Pops a value from the stack, and saves it to the local with the given index.
    ///
    /// # Panics
    /// This function will panic if:
    /// * The stack is empty.
    /// * Attempting to pop a local variable from the stack.
    #[inline]
    pub fn save_to_local(&mut self, idx: usize) {
        let local_idx = self.first_local_idx + idx;
        assert!(
            local_idx < self.end_locals_idx,
            "Attempted to write to a local outside the range of the locals within the stack frame"
        );

        let value = self.pop();

        // SAFETY: If the local is within the locals of the last call to `begin_stack_frame`, `local_idx` must be less
        // than `self.size`, and thus it is within the bounds of `contents`.
        unsafe { self.contents.get_unchecked_mut(local_idx).write(value) };
    }

    /// Pops a value from the stack, and saves it to the local with the given index.
    ///
    /// # Safety
    /// The result of this function is undefined behaviour if calling [`Stack::save_to_local`] with `idx` would panic.
    #[inline]
    pub unsafe fn save_to_local_unchecked(&mut self, idx: usize) {
        let local_idx = self.first_local_idx + idx;
        debug_assert!(
            local_idx < self.end_locals_idx,
            "Attempted to write to a local outside the range of the locals within the stack frame"
        );

        // SAFETY: It is up to the caller to verify that the stack is not empty.
        let value = unsafe { self.pop_unchecked() };

        // SAFETY: If the local is within the locals of the last call to `begin_stack_frame` (as verified by the caller),
        // `local_idx` must be less than `self.size`, and thus it is within the bounds of `contents`.
        unsafe { self.contents.get_unchecked_mut(local_idx).write(value) };
    }

    /// Begins a stack frame with the given number of arguments and number of local variables.
    /// Returns the current stack frame, for returning to.
    ///
    /// # Panics
    /// Calling this function will panic if:
    /// * The stack size is lower than `arg_count`.
    /// * `arg_count` is greater than `local_count`.
    /// * `max_space_required` is less than `local_count`.
    #[inline]
    pub fn begin_new_stack_frame(
        &mut self,
        arg_count: usize,
        local_count: usize,
        max_space_required: usize,
    ) -> Result<StackFrame, RuntimeError> {
        assert!(
            local_count >= arg_count,
            "Cannot have more arguments than local variables"
        );
        assert!(
            self.size >= arg_count,
            "Not enough arguments pushed to stack for stack frame"
        );
        assert!(
            max_space_required >= local_count,
            "Stack frame must require at least `local_count` max space"
        );

        // The index of the first local after the call will be that of the first argument (if any)
        let new_first_local_idx = self.size - arg_count;
        if (self.contents.len() - new_first_local_idx) < max_space_required {
            return Err(RuntimeError::StackOverflow);
        }

        // Store the state that the stack would be in after returning from this call
        let pre_call_frame = StackFrame {
            // The stack size should have the arguments to the function popped from the stack.
            size: new_first_local_idx,
            first_local_idx: self.first_local_idx,
            end_locals_idx: self.end_locals_idx,
        };

        self.first_local_idx = new_first_local_idx;
        self.end_locals_idx = new_first_local_idx + local_count;

        // All of the local variables which are not arguments need a placeholder value to be pushed to stack.
        let additional_values_needed = local_count - arg_count;
        for _ in 0..additional_values_needed {
            // SAFETY: We have verified that there is enough space available on the stack to call the function, as above.
            unsafe { self.push_unchecked(Value::Integer(0)) }
        }

        // Make sure that our size is correct after pushing the placeholders
        debug_assert_eq!(self.size, pre_call_frame.size + local_count);

        Ok(pre_call_frame)
    }

    #[inline]
    fn reduce_size(&mut self, to: usize) {
        while self.size > to {
            self.size -= 1;

            // SAFETY: Since all elements below `self.size` must be inbounds and initialised, this is safe.
            unsafe {
                self.contents
                    .get_unchecked_mut(self.size)
                    .assume_init_drop();
            }
        }
    }

    /// Moves the position of the stack to the given [StackFrame].
    ///
    /// # Panics
    /// This function panics if the given [StackFrame] is above the current size of the stack.
    #[inline]
    pub fn return_to_frame(&mut self, frame: StackFrame) {
        assert!(
            frame.size <= self.size,
            "Cannot pop back to stack frame that is above this one"
        );

        self.reduce_size(self.size - frame.size);

        self.size = frame.size;
        self.first_local_idx = frame.first_local_idx;
        self.end_locals_idx = frame.end_locals_idx;
    }

    /// Pops the return value on the top of the stack, then moves the
    /// position of the stack to the given [StackFrame], and pushes the return value back to the top of the stack.
    ///
    /// # Panics
    /// This function panics if the given [StackFrame] is above the current size of the stack, or if
    /// there is no return value to pop.
    #[inline]
    pub fn return_value_to_frame(&mut self, frame: StackFrame) {
        let value = self.pop(); // Grab the return value

        self.return_to_frame(frame);

        // SAFETY: At least one value was popped from the stack above, so there must be enough space within the stack for the given push.
        unsafe { self.push_unchecked(value) };
    }
}
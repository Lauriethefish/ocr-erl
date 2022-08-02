//! A reference-counted, immutable string type that uses a thin pointer.
//! # Reasoning
//! To store strings within an ERL value without all values requiring a size larger than 16 bytes, we need
//! a string type that takes 8 bytes - one pointer. A reference counted string is also preferred as we don't
//! want to reallocate the string each time it is loaded from a local variable on the stack.
//!
//! This is not possible with an [`std::rc::Rc<str>`], which
//! takes up 16 bytes on the stack as it stores a fat pointer, also containing the length of the string slice.
//! We could use an [`std::rc::Rc<String>`], however this creates double indirection to the string data, and an extra
//! allocation. We also don't need the extra information stored in a string that makes it growable.
//!
//! Luckily, we can work around all this ourselves by storing the size of the slice as well as the data in one allocation
//! on the heap.
//!
//! # Examples
//! Creating and dereferencing an [RcStr]:
//! ```
//! use erl_bytecode_exec::rcstr::RcStr;
//!
//! let example = RcStr::new("Hello World!");
//! assert_eq!("Hello World!", &*example);
//! ```
//!
//! Cloning an [RcStr]:
//! ```
//! use erl_bytecode_exec::rcstr::RcStr;
//!
//! let original = RcStr::new("Clone me!");
//! let clone = original.clone();
//!
//! // Clones do not rely on the lifetime of the original.
//! drop(original);
//!
//! assert_eq!("Clone me!", &*clone);
//! ```
//!
//! Displaying an [RcStr]:
//! ```
//! use erl_bytecode_exec::rcstr::RcStr;
//!
//! let example = RcStr::new("Hello World!");
//!
//! println!("{}", example);
//! println!("{:?}", example);
//! // Both display "Hello World!".
//! ```

use std::{
    alloc::{self, Layout},
    cell::Cell,
    fmt::{Debug, Display},
    mem,
    ops::Deref,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rcstr_size_should_be_arch() {
        assert_eq!(mem::size_of::<usize>(), mem::size_of::<RcStr>());
    }

    #[test]
    fn rcstr_new_should_write_correct_data() {
        let example = RcStr::new("example");
        assert_eq!("example", &*example);
    }

    #[test]
    fn rcstr_new_should_write_correct_length() {
        let example = RcStr::new("example");
        assert_eq!(7, example.header().len);
    }

    #[test]
    fn rcstr_concat_should_write_correct_concatenation() {
        let example = RcStr::concat("Hello ", "World!");
        assert_eq!("Hello World!", &*example);
    }

    #[test]
    fn rcstr_concat_should_write_correct_length() {
        let example = RcStr::concat("Hello ", "World!");
        assert_eq!(12, example.header().len);
    }

    #[test]
    fn rcstr_deref_should_give_slice_with_correct_length() {
        let example = RcStr::new("example");
        assert_eq!(7, Deref::deref(&example).len());
    }

    #[test]
    fn rcstr_new_should_set_1_reference_count() {
        let example = RcStr::new("example");
        assert_eq!(example.header().references.get(), 1);
    }

    #[test]
    fn rcstr_clone_should_increase_reference_count() {
        let example = RcStr::new("example");
        let _clone = example.clone();

        assert_eq!(2, example.header().references.get());
    }

    #[test]
    fn rcstr_drop_should_decrease_reference_count() {
        let example = RcStr::new("example");
        let clone = example.clone();

        drop(example);
        assert_eq!(1, clone.header().references.get());
    }
}

/// A reference-counted string type that uses a thin pointer.
pub struct RcStr {
    ptr: *mut u8,
}

/// The header for the DST that stores the string data.
struct Header {
    /// The length of the string, in bytes.
    len: usize,
    /// The number of remaining references to the string.
    /// Memory should be freed when this reaches 0.
    references: Cell<usize>,
}

/// For visibility purposes, the DST that we will be constructing.
///
/// We can't actually refer to this with a pointer (e.g. `*const VarLengthStr`), since that makes the pointer fat,
/// and one of the main points of this string implementation is that we want thin pointers.
#[repr(C)]
#[allow(unused)]
struct VarLengthStr {
    header: Header,
    data: [u8],
}

impl RcStr {
    /// Creates a new [RcStr], copying the given slice onto the heap.
    /// # Example
    /// ```
    /// use erl_bytecode_exec::rcstr::RcStr;
    ///
    /// let myString = RcStr::new("example");
    /// assert_eq!("example", &*myString);
    /// ```
    #[inline(always)]
    pub fn new(str: &str) -> RcStr {
        let ptr = Self::allocate_and_setup_header(str.len());

        unsafe {
            // SAFETY: The size of the layout used to allocate the pointer in `allocate_and_setup_header` is
            // based on the length of the string, and must be large enough to store the data within the string.
            std::ptr::copy_nonoverlapping(
                str.as_ptr(),
                ptr.add(mem::size_of::<Header>()),
                str.len(),
            );
        }

        RcStr { ptr }
    }

    /// Creates a new [RcStr], containing the right string concatenated to the left string.
    /// This avoids using `format!` and allocating an extra string unnecessarily.
    /// # Example
    /// ```
    /// use erl_bytecode_exec::rcstr::RcStr;
    ///
    /// let myString = RcStr::concat("Hello ", "World!");
    /// assert_eq!("Hello World!", &*myString);
    /// ```
    #[inline(always)]
    pub fn concat(left: &str, right: &str) -> RcStr {
        let ptr = Self::allocate_and_setup_header(left.len() + right.len());

        unsafe {
            let at_left = ptr.add(mem::size_of::<Header>());

            // SAFETY: The size of the layout used to allocate the pointer in `allocate_and_setup_header` is
            // based on the length of both strings, and must be large enough to store the data within both strings.
            std::ptr::copy_nonoverlapping(left.as_ptr(), at_left, left.len());

            let at_right = at_left.add(left.len());
            std::ptr::copy_nonoverlapping(right.as_ptr(), at_right, right.len());
        }

        RcStr { ptr }
    }

    /// Allocates the memory to store a [VarLengthStr] of the given length in bytes.
    #[inline(always)]
    fn allocate_and_setup_header(size: usize) -> *mut u8 {
        unsafe {
            // SAFETY: The layout must not be zero-size, since it includes the [Header], which is not zero sized.
            let ptr = alloc::alloc(Self::get_layout(size));

            // SAFETY: The pointer created has enough space to store a [Header], as defined in the layout.
            // The layout has the alignment of a [Header], so writing one is valid.
            ptr.cast::<Header>().write(Header {
                references: Cell::new(1),
                len: size,
            });

            ptr
        }
    }

    /// Gets the layout for allocating the contained pointer.
    #[inline(always)]
    fn get_layout(size: usize) -> Layout {
        unsafe {
            // The size of the allocated [VarLengthStr].
            // SAFETY: This size is correct as there must be zero padding bytes, since [u8] has 1 alignment.
            let size = mem::size_of::<Header>() + size;

            // SAFETY: `ALIGNMENT` must be a power of 2, since it is the alignment of [Header], fetched using `std::mem::align_of`.
            alloc::Layout::from_size_align_unchecked(size, std::mem::align_of::<Header>())
        }
    }

    /// Fetches the header from the DST pointer.
    #[inline(always)]
    fn header(&self) -> &Header {
        // SAFETY: A valid [Header] is written to this pointer in `new`.
        unsafe { &*self.ptr.cast::<Header>() }
    }
}

impl Clone for RcStr {
    #[inline(always)]
    fn clone(&self) -> Self {
        let references = &self.header().references;
        references.set(references.get() + 1);

        Self { ptr: self.ptr }
    }
}

impl Drop for RcStr {
    #[inline(always)]
    fn drop(&mut self) {
        let header = self.header();
        // After this instance is dropped, the number of references to the contained string will be reduced by 1.
        let remaining = header.references.get() - 1;
        if remaining == 0 {
            unsafe {
                // SAFETY: The memory was allocated with the layout created in `new`, which must be identical to the layout here
                // since the `len` of the string in `new` (passed to `get_layout`) is assigned to the `len` within the [Header], and is not changed until
                // we use it here in the call to `get_layout`
                alloc::dealloc(self.ptr, Self::get_layout(header.len));
            }
        } else {
            header.references.set(remaining);
        }
    }
}

impl Deref for RcStr {
    type Target = str;

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        unsafe {
            // SAFETY: `new` allocates `self.ptr` with enough size to fit [Header] and the number of bytes within the string,
            // which is assigned to the `len` field within the header. The aligment must be valid, as `u8` has alignment of 1.
            let slice = std::slice::from_raw_parts(
                self.ptr.add(mem::size_of::<Header>()),
                self.header().len,
            );

            // SAFETY: `new` fills the content of the type with bytes from a `str`, so it must be valid UTF-8 (since no methods modify
            // or provide mutable access to the contained data)
            std::str::from_utf8_unchecked(slice)
        }
    }
}

impl Display for RcStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self)
    }
}

impl Debug for RcStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self)
    }
}

impl PartialEq for RcStr {
    fn eq(&self, other: &Self) -> bool {
        // Compare the pointers first to speed up comparisons of strings pointing to the same data.
        if self.ptr == other.ptr {
            true
        } else {
            // Otherwise perform a full slice comparison
            *self == *other
        }
    }
}

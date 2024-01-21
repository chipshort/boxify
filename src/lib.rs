#![no_std]
extern crate alloc;

use alloc::{
    alloc::{alloc, alloc_zeroed, handle_alloc_error},
    boxed::Box,
};
use core::{
    alloc::Layout,
    marker::PhantomData,
    mem::{size_of, transmute, MaybeUninit},
    ptr::NonNull,
};

mod compile_tests;

/// Type-checks its argument to be a pointer to some type.
#[doc(hidden)]
#[inline(always)]
pub fn typecheck<T>(_: *mut T) {}

/// Never use this in code that is actually run!
/// This is only here to make sure that the macro works.
/// It creates a second owned value from a reference.
///
/// # Safety
/// This is NEVER safe to use.
#[doc(hidden)]
pub unsafe fn clone<T>(t: &T) -> T {
    let mut dest = MaybeUninit::uninit();
    core::ptr::from_ref(t).copy_to(dest.as_mut_ptr(), 1);
    dest.assume_init()
}

/// A type that can be used as a parameter to infer the type of a value.
/// It can be created from a closure that returns a value of the desired type.
///
/// It allows you to make sure that you have a valid value of `T` or using a
/// value of type `T` to infer the type parameter of a function.
pub struct TypeInferer<T>(PhantomData<T>);

impl<T> TypeInferer<T> {
    /// Creates a new `TypeInferer` from a closure that returns a value of type `T`.
    /// The closure is never called. It's only purpose is to infer the type of `T`.
    pub fn new(_: impl FnOnce() -> T) -> Self {
        Self(PhantomData)
    }
}

/// Helper macro that makes sure that all fields of a struct are being set
/// and returns a `TypeInferer<T>` where `T` is the type of the input value.
#[doc(hidden)]
#[macro_export]
macro_rules! clone_type {
    (
        // match struct instantiation
        $ty:ident {
            $($field:ident : $value:expr),* $(,)?
        }
    ) => {
        // This is never called, but causes a compiler error if
        // not all fields are mentioned
        #[allow(unused)] {
            $crate::TypeInferer::new(|| {
                    $crate::clone_struct!(
                        $ty { }
                        $($field : $value),*
                    )
            })
        }
    };
}

/// Takes an accumulator and a list of fields, cloning each of them (recursively if necessary)
/// by calling [`crate::clone`].
#[doc(hidden)]
#[macro_export]
macro_rules! clone_struct {
    // struct instantiation as a field value
    (
        // accumulator for the cloned fields; gets filled over time
        $clone:ident {
            $($clone_fields:tt)*
        }
        // field: Struct { ... }
        $field:ident : $ty:ident {
            $($fields:tt)*
        },
        $($rest:tt)*
    ) => {
        $crate::clone_struct!(
            $clone {
                // keep everything we already cloned
                $($clone_fields)*
                // clone the new field
                $field : $crate::clone_struct!($ty {}, $ty { $($fields)* }),
            }
            // continue with the rest
            $($rest)*
        )
    };
    // any expression as field value
    (
        // accumulator for the cloned fields; gets filled over time
        $clone:ident {
            $($clone_fields:tt)*
        }
        // field: value
        $field:ident : $value:expr,
        $($rest:tt)*
    ) => {
        $crate::clone_struct!(
            $clone {
                // keep everything we already cloned
                $($clone_fields)*
                // clone the new field
                // SAFETY: this will never be called
                $field : unsafe { $crate::clone(&$value) },
            }
            // continue with the rest
            $($rest)*
        )
    };
    // single field
    (
        // accumulator for the cloned fields; gets filled over time
        $clone: ident {
            $($clone_fields:tt)*
        }
        // field: value
        $field:ident : $value:expr
        // no rest left
    ) => {
        $clone {
            // keep everything we already cloned
            $($clone_fields)*
            // clone the new field
            // SAFETY: this will never be called
            $field : unsafe { $crate::clone(&$value) },
        }
    };
    // no fields
    // TODO: support tuple and unit structs
    ($clone: ident {}) => {
        $clone {}
    };
}

/// Fills a pointer with the given value without allocating memory (if possible).
/// This does not drop the old value.
///
/// # Safety
/// TODO: document safety
#[doc(hidden)]
#[macro_export]
macro_rules! fill_ptr {
    // [v; n]
    ($ptr: expr, [$v:expr; $n:expr]) => {{
        let boxify_ptr = $ptr;
        $crate::typecheck(boxify_ptr);

        $crate::fill_array(boxify_ptr, $v);
    }};
    // Strct { ... }
    (
        $ptr: expr,
        $ty:ident {
            $($fields:tt)*
        }
    ) => {{
        // We don't need to assert that all fields are set because that's already done in `boxify`.
        // $crate::clone_type!($ty { $($fields)* });

        $crate::init_fields!($ptr, $($fields)*);
    }};
    // TODO: enums

    // catch-all
    ($ptr:expr, $value:expr) => {{
        let boxify_ptr = $ptr;
        $crate::typecheck(boxify_ptr);
        // simplest version is just to write to the ptr
        boxify_ptr.write($value);
    }};
}

#[macro_export]
macro_rules! boxify {
    // [0; COUNT]
    ([0; $n:expr]) => {
        // Rust uses i32 for untyped integer literals
        unsafe { $crate::new_box_zeroed::<[i32; $n]>() }
    };
    ([0u16; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[u16; $n]>() }
    };
    ([0u32; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[u32; $n]>() }
    };
    ([0u64; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[u64; $n]>() }
    };
    ([0u128; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[u128; $n]>() }
    };
    ([0usize; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[usize; $n]>() }
    };
    ([0i16; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[i16; $n]>() }
    };
    ([0i32; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[i32; $n]>() }
    };
    ([0i64; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[i64; $n]>() }
    };
    ([0i128; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[i128; $n]>() }
    };
    ([0isize; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[isize; $n]>() }
    };
    ([0f32; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[f32; $n]>() }
    };
    ([0f64; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[f64; $n]>() }
    };
    ([false; $n:expr]) => {
        unsafe { $crate::new_box_zeroed::<[bool; $n]>() }
    };
    // [value; COUNT] where TypeOf[value]: Copy
    ([$value:expr; $n:expr]) => {
        $crate::new_filled_boxed_array::<_, $n>($value)
    };
    // Struct { ... }
    ($ty:ident { $($fields:tt)* }) => {{
        let mut boxify_final_value = $crate::new_box_uninit_typed($crate::clone_type!($ty { $($fields)* }));
        let boxify_final_value_ptr = boxify_final_value.as_mut_ptr();

        #[allow(unused_unsafe)]
        unsafe { $crate::fill_ptr!(boxify_final_value_ptr, $ty { $($fields)* }) };

        // SAFETY: we just initialized the struct
        unsafe { $crate::assume_init(boxify_final_value) }
    }};
}

#[macro_export]
macro_rules! init_fields {
    // struct instantiation as a field value
    (
        $ptr: expr,
        // field: Struct { ... }
        $field:ident : $ty:ident {
            $($fields:tt)*
        },
        $($rest:tt)*
    ) => {{
        // fill the field with the struct
        unsafe {
            $crate::fill_ptr!(core::ptr::addr_of_mut!((*$ptr).$field), $ty { $($fields)* });
        }

        $crate::init_fields!($ptr, $($rest)*);
    }};
    // array as field value
    (
        $ptr: expr,
        // field: [value; COUNT]
        $field:ident : [$value:expr; $n:expr],
        $($rest:tt)*
    ) => {
        // SAFETY: according to the `MaybeUninit` docs, this is safe
        unsafe {
            $crate::fill_ptr!(core::ptr::addr_of_mut!((*$ptr).$field), [$value; $n]);
        }

        $crate::init_fields!($ptr, $($rest)*);
    };
    // any expression as field value
    (
        $ptr: expr,
        $field:ident : $value:expr,
        $($rest:tt)*
    ) => {
        // SAFETY: according to the `MaybeUninit` docs, this is safe
        unsafe {
            $crate::fill_ptr!(core::ptr::addr_of_mut!((*$ptr).$field), $value);
        }

        $crate::init_fields!($ptr, $($rest)*);
    };
    // single field
    (
        $ptr: expr,
        $field:ident : $value:expr
    ) => {
        init_fields!($ptr, $field: $value,);
    };
    // no fields
    ($ptr: expr,) => {};
}

/// Allocates a new box of the given type, leaving the memory uninitialized.
/// This version takes a closure to avoid having to specify the type. The closure itself is not called.
///
/// This can be replaced with `Box::new_uninit` once it is stable.
#[doc(hidden)]
pub fn new_box_uninit_typed<T>(_: TypeInferer<T>) -> Box<MaybeUninit<T>> {
    new_box_uninit::<T>()
}

/// Allocates a new box of the given type, leaving the memory uninitialized.
///
/// This can be replaced with `Box::new_uninit` once it is stable.
#[doc(hidden)]
pub fn new_box_uninit<T>() -> Box<MaybeUninit<T>> {
    let ptr = if size_of::<T>() == 0 {
        NonNull::dangling()
    } else {
        let layout = Layout::new::<MaybeUninit<T>>();
        // SAFETY: alloc is safe because we checked T for ZST and MaybeUninit<T> has the same layout as T
        let ptr = unsafe { alloc(layout) } as *mut MaybeUninit<T>;
        if ptr.is_null() {
            handle_alloc_error(layout);
        }
        // SAFETY: We just made sure it's non-null
        unsafe { NonNull::new_unchecked(ptr) }
    };
    unsafe { Box::from_raw(ptr.as_ptr()) }
}

/// Allocates a new box of the given type, filling it with the given value.
#[doc(hidden)]
pub fn new_filled_boxed_array<T: Copy, const SIZE: usize>(value: T) -> Box<[T; SIZE]> {
    let mut b = new_box_uninit::<[T; SIZE]>();

    // SAFETY: `new_box_uninit` returns an uninitialized box
    unsafe { fill_array(b.as_mut_ptr(), value) };

    // SAFETY: b is initialized above
    unsafe { assume_init(b) }
}

/// Allocates a new box of the given type, zeroing out the memory.
/// Currently this is probably not more efficient than [`new_filled_boxed_array`] with a value of `0`,
/// but it might be in the future, when the Allocator API stabilizes.
/// This is because we can then avoid zeroing the memory twice for allocators that always zero it out anyways.
///
/// # Safety
/// All-zero bytes must be a valid value of type `T`.
#[doc(hidden)]
pub unsafe fn new_box_zeroed<T>() -> Box<T> {
    let ptr = if size_of::<T>() == 0 {
        NonNull::dangling()
    } else {
        let layout = Layout::new::<MaybeUninit<T>>();
        // SAFETY: alloc is safe because we checked T for ZST and MaybeUninit<T> has the same layout as T
        let ptr = unsafe { alloc_zeroed(layout) as *mut MaybeUninit<T> };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }
        // SAFETY: We just made sure it's non-null
        unsafe { NonNull::new_unchecked(ptr) }
    };
    unsafe { Box::from_raw(ptr.as_ptr() as *mut T) }
}

// TODO: use trait for specialization? (e.g. for `T: Clone` instead of `Copy`, we need to clone each time)
/// Fills a boxed array with the given value.
///
/// # Safety
/// `b` must not be initialized yet. Otherwise, it's `Drop` implementation will not be called.
#[inline(always)]
#[doc(hidden)]
pub unsafe fn fill_array<T: Copy, const SIZE: usize>(array: *mut [T; SIZE], value: T) {
    // get the raw pointer to the array
    let array = array as *mut T;

    if size_of::<T>() == 1 {
        // in this case, we can use `ptr::write_bytes` instead of `ptr::write`
        // SAFETY: we just checked that T is 1 byte, so transmuting to u8 is safe
        let value_byte = core::ptr::addr_of!(value) as *const u8;
        core::ptr::write_bytes(array, *value_byte, SIZE);
    } else {
        for i in 0..SIZE {
            // write the value to the array
            array.add(i).write(value);
        }
    }
}

/// Converts a `Box<MaybeUninit<T>>` to a `Box<T>`.
///
/// # Safety
/// `b` must be initialized.
#[doc(hidden)]
pub unsafe fn assume_init<T>(b: Box<MaybeUninit<T>>) -> Box<T> {
    // SAFETY: MaybeUninit<T> guarantees the same layout as T
    transmute(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Size that is too big to allocate on the stack
    #[cfg(miri)]
    const SIZE: usize = 10;
    #[cfg(not(miri))]
    const SIZE: usize = 10000000;

    #[test]
    #[ignore = "causes stack overflow"]
    fn size_too_big_for_stack() {
        let b = Box::new([0u8; SIZE]);
        assert_eq!(b[SIZE - 1], 0);
    }

    #[test]
    fn new_box_uninit_not_on_stack() {
        new_box_uninit::<[u8; SIZE]>();
    }

    #[test]
    fn boxify_zeroed_array() {
        // this should not:
        let b = boxify!([0; SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], 0);
        }
        let b = boxify!([0i128; SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], 0);
        }
        let b = boxify!([0u64; SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], 0);
        }
        let b = boxify!([0f64; SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], 0.0);
        }
    }

    #[test]
    fn boxify_single_byte_array() {
        // bool
        let b = boxify!([false; SIZE]);
        for i in 0..SIZE {
            assert!(!b[i]);
        }
        let b = boxify!([true; SIZE]);
        for i in 0..SIZE {
            assert!(b[i]);
        }
        // u8
        let b = boxify!([42u8; SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], 42);
        }
        // single byte struct
        #[repr(transparent)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct Foo(u8);
        let b = boxify!([Foo(42); SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], Foo(42));
        }
    }

    #[test]
    fn boxify_multi_byte_array() {
        let b = boxify!([4200; SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], 4200);
        }
        let b = boxify!([i128::MAX / 42; SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], i128::MAX / 42);
        }
        // multi byte struct
        #[repr(transparent)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct Foo(u64);
        let b = boxify!([Foo(0x8888888888); SIZE]);
        for i in 0..SIZE {
            assert_eq!(b[i], Foo(0x8888888888));
        }
    }

    #[test]
    fn boxify_zst_array() {
        // just making sure these don't cause problems
        let b = boxify!([(); SIZE]);
        assert_eq!(b.len(), SIZE);

        let b = boxify!([(); 0]);
        assert_eq!(b.len(), 0);

        let b = boxify!([12u8; 0]);
        assert_eq!(b.len(), 0);
    }

    #[test]
    fn boxify_struct() {
        #[derive(Debug, Clone, Copy, PartialEq)]
        struct Foo {
            a: u32,
            b: u32,
        }
        let b = boxify!(Foo { a: 1, b: 2 });
        assert_eq!(b.a, 1);
        assert_eq!(b.b, 2);

        #[derive(Debug, PartialEq)]
        struct Bar {
            a: [u32; SIZE],
            b: [Foo; SIZE],
        }
        let b = boxify!(Bar {
            a: [0; SIZE],
            b: [Foo { a: 1, b: 2 }; SIZE],
        });
        assert_eq!(b.a[SIZE - 1], 0);
        assert_eq!(b.b[SIZE - 1], Foo { a: 1, b: 2 });

        struct Nested {
            a: Bar,
            b: [u32; SIZE],
        }
        let b = boxify!(Nested {
            a: Bar {
                a: [0; SIZE],
                b: [Foo { a: 1, b: 2 }; SIZE],
            },
            b: [0; SIZE],
        });
        assert_eq!(b.a.a[SIZE - 1], 0);
        assert_eq!(b.a.b[SIZE - 1], Foo { a: 1, b: 2 });
    }

    // #[test]
    // fn boxify_tuple() {
    //     // actual tuple
    //     let b = boxify!((1, 2));
    //     assert_eq!(b.0, 1);
    //     assert_eq!(b.1, 2);

    //     // tuple struct
    //     let b = boxify!(Some(1));
    //     assert_eq!(b, Some(1));
    // }

    #[test]
    fn boxify_complex_struct() {
        struct A<'a, T> {
            a: &'a [T; 100],
            b: &'a str,
            c: [T; 10],
        }

        let a = &[42; 100];
        let b = "hello world";
        let bx = boxify!(A {
            a: a,
            b: b,
            c: [21; 10]
        }); // TODO: support short form `A { a, b }`
        assert_eq!(bx.a, a);
        assert_eq!(bx.b, b);
    }

    #[test]
    fn boxify_local_variable() {
        let a = alloc::vec![42; 100];
        // let b = boxify!(a);
        // assert_eq!(*b, 42);

        struct Test {
            a: alloc::vec::Vec<u32>,
        }

        boxify!(Test { a: a });
    }
}

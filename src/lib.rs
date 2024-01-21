#![no_std]
extern crate alloc;

use alloc::{
    alloc::{alloc, alloc_zeroed, handle_alloc_error},
    boxed::Box,
};
use core::{
    alloc::Layout,
    mem::{size_of, transmute, MaybeUninit},
    ptr::NonNull,
};

/// Type-checks its argument to be a pointer to some type.
#[doc(hidden)]
#[inline(always)]
pub fn typecheck<T>(_: *mut T) {}

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
        let ptr = $ptr;
        $crate::typecheck(ptr);

        $crate::fill_array(ptr, $v);
    }};
    // Strct { ... }
    ($ptr: expr, $ty:ident { $($fields:tt)* }) => {{
        // This is never called, but causes a compiler error if
        // not all fields are initialized
        #[allow(unused)] {
            || {
                $ty {
                    $($fields)*
                }
            };
        }

        $crate::init_fields!($ptr, $($fields)*);
    }};
    // TODO: enums

    // catch-all
    ($ptr:expr, $value:expr) => {{
        let ptr = $ptr;
        $crate::typecheck(ptr);
        // simplest version is just to write to the ptr
        ptr.write($value);
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
        let mut v = $crate::new_box_uninit::<$ty>();
        let ptr = v.as_mut_ptr();

        #[allow(unused_unsafe)]
        unsafe { $crate::fill_ptr!(ptr, $ty { $($fields)* }) };

        // SAFETY: we just initialized the struct
        unsafe { $crate::assume_init(v) }
    }};
}

#[macro_export]
macro_rules! init_fields {
    // struct instantiation as a field value
    ($ptr: expr, $field:ident : $ty:ident { $($fields:tt)* }, $($rest:tt)*) => {{
        // fill the field with the struct
        unsafe {
            $crate::fill_ptr!(core::ptr::addr_of_mut!((*$ptr).$field), $ty { $($fields)* });
        }

        $crate::init_fields!($ptr, $($rest)*);
    }};
    // array as field value
    ($ptr: expr, $field:ident : [$value:expr; $n:expr], $($rest:tt)*) => {
        // SAFETY: according to the `MaybeUninit` docs, this is safe
        unsafe {
            $crate::fill_ptr!(core::ptr::addr_of_mut!((*$ptr).$field), [$value; $n]);
        }

        $crate::init_fields!($ptr, $($rest)*);
    };
    // any expression as field value
    ($ptr: expr, $field:ident : $value:expr, $($rest:tt)*) => {
        // SAFETY: according to the `MaybeUninit` docs, this is safe
        unsafe {
            $crate::fill_ptr!(core::ptr::addr_of_mut!((*$ptr).$field), $value);
        }

        $crate::init_fields!($ptr, $($rest)*);
    };
    ($ptr: expr, $field:ident : $value:expr) => {
        init_fields!($ptr, $field: $value,);
    };
    // no more fields
    ($ptr: expr,) => {};
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

    #[test]
    fn boxify_complex_struct() {
        struct A<'a> {
            a: &'a [u32; 100],
            b: &'a str,
        }

        let a = &[42; 100];
        let b = "hello world";
        let bx = boxify!(A { a: a, b: b }); // TODO: support short form `A { a, b }`
        assert_eq!(bx.a, a);
        assert_eq!(bx.b, b);
    }
}

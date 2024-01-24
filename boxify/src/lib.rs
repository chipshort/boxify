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

pub use boxify_macro::boxify;

/// Never use this in code that is actually run!
/// It creates a second owned value from a reference.
///
/// This crate only calls it in closures that are never called themselves.
/// It is only needed to typecheck the macro input.
///
/// # Safety
/// This is NEVER safe to use.
#[doc(hidden)]
pub unsafe fn clone<T>(t: &T) -> T {
    let mut dest = MaybeUninit::uninit();
    (t as *const T).copy_to(dest.as_mut_ptr(), 1);
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

/// Allocates a new box of the given type, leaving the memory uninitialized.
/// This version takes a closure to avoid having to specify the type. The closure itself is not called.
///
/// This can be replaced with `Box::new_uninit` once it is stable.
#[doc(hidden)]
pub fn new_box_uninit_typed<T>(_: TypeInferer<T>) -> Box<MaybeUninit<T>> {
    new_box_uninit::<T>()
}

/// See [`new_box_zeroed`] and [`new_box_uninit_typed`].
#[doc(hidden)]
pub unsafe fn new_box_zeroed_typed<T>(_: TypeInferer<T>) -> Box<T> {
    new_box_zeroed()
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

/// Allocates a new box of the given type, zeroing out the memory.
/// Currently this is probably not more efficient than [`fill_array`] with a value of `0`,
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

/// Fills a boxed array with the given value.
///
/// # Safety
/// `array` must not be initialized yet. Otherwise, it's `Drop` implementation will not be called.
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
    // maybe this would be better?
    // Box::from_raw((*Box::into_raw(b)).as_mut_ptr())
}

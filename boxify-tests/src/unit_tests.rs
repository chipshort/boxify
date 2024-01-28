#![cfg(test)]

use boxify::boxify;

/// Size that is too big to allocate on the stack
#[cfg(miri)]
const SIZE: usize = 10;
#[cfg(not(miri))]
const SIZE: usize = 10000000;

#[test]
#[ignore = "Box::new causes stack overflow"]
fn size_too_big_for_stack() {
    let b = Box::new([0u8; SIZE]);
    assert_eq!(b[SIZE - 1], 0);
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
fn boxify_struct_in_module() {
    mod foo {
        #[derive(Debug, PartialEq)]
        pub struct Foo {
            pub a: u32,
            pub b: u32,
        }
    }
    let b = boxify!(foo::Foo { a: 1, b: 2 });
    assert_eq!(b.a, 1);
    assert_eq!(b.b, 2);
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
fn boxify_tuple() {
    // actual tuple
    let b = boxify!(([0u64; SIZE], 2));
    assert_eq!(b.0[0], 0);
    assert_eq!(b.1, 2);

    // tuple struct
    struct TupleStruct([u64; SIZE], u32);
    let b = boxify!(TupleStruct([0u64; SIZE], 2));
    assert_eq!(b.0[0], 0);
    assert_eq!(b.1, 2);
}

#[test]
fn boxify_fn_call() {
    fn test() -> [u32; 100] {
        [42; 100]
    }
    // nested
    struct A {
        a: [u32; 100],
    }
    let b = boxify!(A { a: test() });
    assert_eq!(b.a[0], 42);

    // top level
    let b = boxify!(test());
    assert_eq!(b[0], 42);

    // parameter
    fn test2(v: i32) -> [i32; 100] {
        [v; 100]
    }
    let b = boxify!(test2(42));
    assert_eq!(b[0], 42);

    // generic
    fn test_generic<T: Copy>(v: T) -> [T; 100] {
        [v; 100]
    }
    let b = boxify!(test_generic(21));
    assert_eq!(b[0], 21);
}

#[test]
fn boxify_complex_struct() {
    struct A<'a, T> {
        a: &'a [T; 100],
        b: &'a str,
        c: [T; 10],
    }

    let a = &[42; 100];
    let b = "hello world";
    let bx = boxify!(A { a, b, c: [21; 10] });
    assert_eq!(bx.a, a);
    assert_eq!(bx.b, b);
}

#[test]
fn boxify_generic_tuple_struct() {
    struct A<'a, T>(&'a [T; 100]);

    let a = &[42; 100];
    let bx = boxify!(A(a));
    assert_eq!(bx.0, a);
}

#[test]
fn boxify_local_variable() {
    let a = vec![42; 100];
    // let b = boxify!(a);
    // assert_eq!(*b, 42);

    struct Test {
        a: Vec<u32>,
    }

    boxify!(Test { a: a });
}

#[test]
fn boxify_different_reprs() {
    #[repr(C)]
    struct FooC {
        a: u8,
        b: u32,
    }
    #[repr(packed)]
    struct FooP {
        a: u8,
        b: Box<u32>,
    }

    struct NotCopy<T>(T);

    #[repr(C, packed)]
    struct FooP2 {
        a: NotCopy<u16>,
        b: NotCopy<[u32; 5]>,
    }

    let b = boxify!(FooC { a: 1, b: 2 });
    assert_eq!(b.a, 1);
    assert_eq!(b.b, 2);

    let bx = Box::new(42);
    let b = boxify!(FooP { a: 1, b: bx });
    assert_eq!(b.a, 1);
    assert_eq!(*b.b, 42);

    let b = boxify!(FooP2 {
        a: NotCopy(1u16),
        b: NotCopy([42; 5]),
    });
    let a = b.a;
    assert_eq!(a.0, 1);
    let b = unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(b.b)) };
    assert_eq!(b.0, [42; 5]); // TODO: unaligned
}

#[test]
fn boxify_outer_var() {
    struct NotCopy(u32);
    struct Foo {
        a: NotCopy,
    }
    let a = NotCopy(42);

    let b = boxify!(Foo { a });
    assert_eq!(b.a.0, 42);
}

#[test]
fn boxify_spread_syntax() {
    struct A {
        a: u32,
        b: u32,
    }

    let b = boxify!(A {
        a: 1,
        ..A {
            b: 2,
            ..A { a: 3, b: 4 }
        }
    });

    assert_eq!(b.a, 1);
    assert_eq!(b.b, 2); // FIXME: uninitialized memory
}

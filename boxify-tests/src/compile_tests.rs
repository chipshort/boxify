//! Tests that should fail to compile.

/// ```compile_fail
/// use boxify::boxify;
///
/// struct Foo {
///    bar: i32,
/// }
///
/// boxify!(Foo {})
/// ```
#[allow(dead_code)]
fn missing_struct_field() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// let a = vec![42; 100];
/// let b = boxify!(a);
/// ```
#[allow(dead_code)]
fn incorrect_input_type() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// let b = boxify!((|| 42)()); // TODO: this should also work
/// ```
#[allow(dead_code)]
fn function_call() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// #[allow(non_camel_case_types)]
/// struct test(u32);
///
/// let b = boxify!(test(42));
/// ```
#[allow(dead_code)]
fn lower_case_tuple_struct() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// struct A(u32);
/// fn Test(_: u32) -> A { A(42) }
///
/// let b = boxify!(Test(42));
/// ```
#[allow(dead_code)]
fn upper_case_fn_call() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// enum Foo {
///    Bar,
/// }
/// let b = boxify!(Foo::Bar);
/// ```
#[allow(dead_code)]
fn enum_() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// enum Foo {
///    Bar(u32),
/// }
/// let b = boxify!(Foo::Bar(0));
/// ```
#[allow(dead_code)]
fn enum_data1() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// enum Foo {
///    Bar { a: u32 },
/// }
/// let b = boxify!(Foo::Bar { a: 42 });
/// ```
#[allow(dead_code)]
fn enum_data2() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// struct A {
///     a: u32,
///     b: u32,
/// }
///
/// let b = boxify!(A {
///     a: 1,
///     ..A {
///         b: 2,
///         ..A { a: 3, b: 4 }
///     }
/// });
#[allow(dead_code)]
fn struct_update_syntax() {}

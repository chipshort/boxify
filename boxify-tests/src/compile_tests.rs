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
/// let b = boxify!((|| 42)());
/// ```
#[allow(dead_code)]
fn function_call() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// fn test() -> [i32; 100] {
///    [42; 100]
/// }
/// let b = boxify!(test());
/// ```
#[allow(dead_code)]
fn function_call_empty() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// fn test() -> [u32; 100] {
///     [42; 100]
/// }
/// struct A {
///     a: [u32; 100],
/// }
///
/// struct IsNotFn<T>(core::marker::PhantomData<T>);
///
/// // TODO: this should call the function instead of failing
/// // Problem: How to detect if it's a function call or a tuple struct?
/// let _ = boxify!(A { a: test() });
/// ```
#[allow(dead_code)]
fn function_call_inside() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// fn test(v: i32) -> [i32; 100] {
///    [v; 100]
/// }
/// let b = boxify!(test(42));
/// ```
#[allow(dead_code)]
fn function_call_param() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// fn test<T>(v: T) -> [i32; 100] {
///   [42; 100]
/// }
/// let b = boxify!(test(42));
///
#[allow(dead_code)]
fn function_call_generics() {}

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

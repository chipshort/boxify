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
/// fn test() -> [i32; 100] {
///    [42; 100]
/// }
/// let b = boxify!(test());
/// ```
#[allow(dead_code)]
fn function_call_empty() {}

/// ```compile_fail
/// use boxify::boxify;
/// fn test(v: i32) -> [i32; 100] {
///    [v; 100]
/// }
/// let b = boxify!(test(42));
/// ```
#[allow(dead_code)]
fn function_call_param() {}

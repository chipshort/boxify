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
pub fn missing_struct_field() {}

/// ```compile_fail
/// use boxify::boxify;
///
/// let a = vec![42; 100];
/// let b = boxify!(a);
/// ```
pub fn incorrect_usage() {}

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

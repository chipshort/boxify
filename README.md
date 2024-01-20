# boxify

This crate provides a macro to initialize your `Box<T>` on the heap without having to have it on the stack before.
This allows easily putting big arrays or structs containing them into a `Box` without overflowing the stack:

```rust
// this would overflow the stack:
// let e = Box::new(Example {
//     huge_array: [42; 1024 * 1024 * 1024],
// });

// this does not:
let e = boxify::boxify!(Example {
    huge_array: [42; 1024 * 1024 * 1024],
});
```

## Supported structures

Currently, this supports structs and arrays. All other types are constructed on the stack and put into the box later.

Support for enums is currently not there yet, but planned.
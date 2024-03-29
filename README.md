# boxify

This crate provides a macro to initialize your `Box<T>` on the heap without having to have it on the stack before.
This allows easily putting big arrays or structs containing them into a `Box` without overflowing the stack:

```rust ,ignore
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

Currently, this supports tuples, arrays and structs, even deeply nested ones. Take a look at the `examples` folder to
see what's possible.
All other types are constructed on the stack and put into the box later.

## Known Limitations

- Enums are not supported and can never be fully supported since their layout in memory is not fully specified.
- Only calls of _lowercase_ function names and _uppercase_ tuple struct instantiations are fully supported.  
  This limitation is necessary because there is no way to determine whether something is a function call or a tuple struct instantiation and both have to be handled differently, so this crate just uses the naming as a heuristic.
  The macro will cause a compiler error if it encounters a function where a struct was expected to prevent unsoundness.
  A lowercase tuple struct instantiation will quietly allocate on the stack and move it to the heap.
- Struct update syntax, aka `Test { ..test }` is not allowed and causes a compiler error.
  This is because the macro needs to know all of the struct fields to fill them.

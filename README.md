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

Currently, this supports structs and arrays, even deeply nested ones. Take a look at the `examples` folder to
see what's possible.
All other types are constructed on the stack and put into the box later.

Support for enums is currently not there yet, but planned.

## Known Limitations

- Structs need to be imported in order to be instantiated, you cannot instantiate `module::Struct` without importing it:

```rust
use module::Struct;

boxify::boxify!(Struct { a: 42 });
// this does not work:
// boxify::boxify!(module::Struct { a: 42 });
```

- Currently, you cannot use the short instantiation syntax:

```rust
boxify::boxify!(Struct { a: a });
// this does not work:
// boxify::boxify!(Struct { a });
```

- Enums are not supported (yet)
<div align="center">
<h1>generic-arraydeque</h1>
</div>
<div align="center">

A fixed-capacity, stack-allocated double-ended queue (deque) backed by `generic-array`.

[<img alt="github" src="https://img.shields.io/badge/github-al8n/generic--arraydeque-8da0cb?style=for-the-badge&logo=Github" height="22">][Github-url]
<img alt="LoC" src="https://img.shields.io/endpoint?url=https%3A%2F%2Fgist.githubusercontent.com%2Fal8n%2F327b2a8aef9003246e45c6e47fe63937%2Fraw%2Fgeneric-arraydeque" height="22">
[<img alt="Build" src="https://img.shields.io/github/actions/workflow/status/al8n/generic-arraydeque/ci.yml?logo=Github-Actions&style=for-the-badge" height="22">][CI-url]
[<img alt="codecov" src="https://img.shields.io/codecov/c/gh/al8n/generic-arraydeque?style=for-the-badge&token=6R3QFWRWHL&logo=codecov" height="22">][codecov-url]

[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-generic--arraydeque-66c2a5?style=for-the-badge&labelColor=555555&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">][doc-url]
[<img alt="crates.io" src="https://img.shields.io/crates/v/generic-arraydeque?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0iaXNvLTg4NTktMSI/Pg0KPCEtLSBHZW5lcmF0b3I6IEFkb2JlIElsbHVzdHJhdG9yIDE5LjAuMCwgU1ZHIEV4cG9ydCBQbHVnLUluIC4gU1ZHIFZlcnNpb246IDYuMDAgQnVpbGQgMCkgIC0tPg0KPHN2ZyB2ZXJzaW9uPSIxLjEiIGlkPSJMYXllcl8xIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHhtbG5zOnhsaW5rPSJodHRwOi8vd3d3LnczLm9yZy8xOTk5L3hsaW5rIiB4PSIwcHgiIHk9IjBweCINCgkgdmlld0JveD0iMCAwIDUxMiA1MTIiIHhtbDpzcGFjZT0icHJlc2VydmUiPg0KPGc+DQoJPGc+DQoJCTxwYXRoIGQ9Ik0yNTYsMEwzMS41MjgsMTEyLjIzNnYyODcuNTI4TDI1Niw1MTJsMjI0LjQ3Mi0xMTIuMjM2VjExMi4yMzZMMjU2LDB6IE0yMzQuMjc3LDQ1Mi41NjRMNzQuOTc0LDM3Mi45MTNWMTYwLjgxDQoJCQlsMTU5LjMwMyw3OS42NTFWNDUyLjU2NHogTTEwMS44MjYsMTI1LjY2MkwyNTYsNDguNTc2bDE1NC4xNzQsNzcuMDg3TDI1NiwyMDIuNzQ5TDEwMS44MjYsMTI1LjY2MnogTTQzNy4wMjYsMzcyLjkxMw0KCQkJbC0xNTkuMzAzLDc5LjY1MVYyNDAuNDYxbDE1OS4zMDMtNzkuNjUxVjM3Mi45MTN6IiBmaWxsPSIjRkZGIi8+DQoJPC9nPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPC9zdmc+DQo=" height="22">][crates-url]
[<img alt="crates.io" src="https://img.shields.io/crates/d/generic-arraydeque?color=critical&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBzdGFuZGFsb25lPSJubyI/PjwhRE9DVFlQRSBzdmcgUFVCTElDICItLy9XM0MvL0RURCBTVkcgMS4xLy9FTiIgImh0dHA6Ly93d3cudzMub3JnL0dyYXBoaWNzL1NWRy8xLjEvRFREL3N2ZzExLmR0ZCI+PHN2ZyB0PSIxNjQ1MTE3MzMyOTU5IiBjbGFzcz0iaWNvbiIgdmlld0JveD0iMCAwIDEwMjQgMTAyNCIgdmVyc2lvbj0iMS4xIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHAtaWQ9IjM0MjEiIGRhdGEtc3BtLWFuY2hvci1pZD0iYTMxM3guNzc4MTA2OS4wLmkzIiB3aWR0aD0iNDgiIGhlaWdodD0iNDgiIHhtbG5zOnhsaW5rPSJodHRwOi8vd3d3LnczLm9yZy8xOTk5L3hsaW5rIj48ZGVmcz48c3R5bGUgdHlwZT0idGV4dC9jc3MiPjwvc3R5bGU+PC9kZWZzPjxwYXRoIGQ9Ik00NjkuMzEyIDU3MC4yNHYtMjU2aDg1LjM3NnYyNTZoMTI4TDUxMiA3NTYuMjg4IDM0MS4zMTIgNTcwLjI0aDEyOHpNMTAyNCA2NDAuMTI4QzEwMjQgNzgyLjkxMiA5MTkuODcyIDg5NiA3ODcuNjQ4IDg5NmgtNTEyQzEyMy45MDQgODk2IDAgNzYxLjYgMCA1OTcuNTA0IDAgNDUxLjk2OCA5NC42NTYgMzMxLjUyIDIyNi40MzIgMzAyLjk3NiAyODQuMTYgMTk1LjQ1NiAzOTEuODA4IDEyOCA1MTIgMTI4YzE1Mi4zMiAwIDI4Mi4xMTIgMTA4LjQxNiAzMjMuMzkyIDI2MS4xMkM5NDEuODg4IDQxMy40NCAxMDI0IDUxOS4wNCAxMDI0IDY0MC4xOTJ6IG0tMjU5LjItMjA1LjMxMmMtMjQuNDQ4LTEyOS4wMjQtMTI4Ljg5Ni0yMjIuNzItMjUyLjgtMjIyLjcyLTk3LjI4IDAtMTgzLjA0IDU3LjM0NC0yMjQuNjQgMTQ3LjQ1NmwtOS4yOCAyMC4yMjQtMjAuOTI4IDIuOTQ0Yy0xMDMuMzYgMTQuNC0xNzguMzY4IDEwNC4zMi0xNzguMzY4IDIxNC43MiAwIDExNy45NTIgODguODMyIDIxNC40IDE5Ni45MjggMjE0LjRoNTEyYzg4LjMyIDAgMTU3LjUwNC03NS4xMzYgMTU3LjUwNC0xNzEuNzEyIDAtODguMDY0LTY1LjkyLTE2NC45MjgtMTQ0Ljk2LTE3MS43NzZsLTI5LjUwNC0yLjU2LTUuODg4LTMwLjk3NnoiIGZpbGw9IiNmZmZmZmYiIHAtaWQ9IjM0MjIiIGRhdGEtc3BtLWFuY2hvci1pZD0iYTMxM3guNzc4MTA2OS4wLmkwIiBjbGFzcz0iIj48L3BhdGg+PC9zdmc+&style=for-the-badge" height="22">][crates-url]
<img alt="license" src="https://img.shields.io/badge/License-Apache%202.0/MIT-blue.svg?style=for-the-badge&fontColor=white&logoColor=f5c076&logo=data:image/svg+xml;base64,PCFET0NUWVBFIHN2ZyBQVUJMSUMgIi0vL1czQy8vRFREIFNWRyAxLjEvL0VOIiAiaHR0cDovL3d3dy53My5vcmcvR3JhcGhpY3MvU1ZHLzEuMS9EVEQvc3ZnMTEuZHRkIj4KDTwhLS0gVXBsb2FkZWQgdG86IFNWRyBSZXBvLCB3d3cuc3ZncmVwby5jb20sIFRyYW5zZm9ybWVkIGJ5OiBTVkcgUmVwbyBNaXhlciBUb29scyAtLT4KPHN2ZyBmaWxsPSIjZmZmZmZmIiBoZWlnaHQ9IjgwMHB4IiB3aWR0aD0iODAwcHgiIHZlcnNpb249IjEuMSIgaWQ9IkNhcGFfMSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIiB4bWxuczp4bGluaz0iaHR0cDovL3d3dy53My5vcmcvMTk5OS94bGluayIgdmlld0JveD0iMCAwIDI3Ni43MTUgMjc2LjcxNSIgeG1sOnNwYWNlPSJwcmVzZXJ2ZSIgc3Ryb2tlPSIjZmZmZmZmIj4KDTxnIGlkPSJTVkdSZXBvX2JnQ2FycmllciIgc3Ryb2tlLXdpZHRoPSIwIi8+Cg08ZyBpZD0iU1ZHUmVwb190cmFjZXJDYXJyaWVyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiLz4KDTxnIGlkPSJTVkdSZXBvX2ljb25DYXJyaWVyIj4gPGc+IDxwYXRoIGQ9Ik0xMzguMzU3LDBDNjIuMDY2LDAsMCw2Mi4wNjYsMCwxMzguMzU3czYyLjA2NiwxMzguMzU3LDEzOC4zNTcsMTM4LjM1N3MxMzguMzU3LTYyLjA2NiwxMzguMzU3LTEzOC4zNTcgUzIxNC42NDgsMCwxMzguMzU3LDB6IE0xMzguMzU3LDI1OC43MTVDNzEuOTkyLDI1OC43MTUsMTgsMjA0LjcyMywxOCwxMzguMzU3UzcxLjk5MiwxOCwxMzguMzU3LDE4IHMxMjAuMzU3LDUzLjk5MiwxMjAuMzU3LDEyMC4zNTdTMjA0LjcyMywyNTguNzE1LDEzOC4zNTcsMjU4LjcxNXoiLz4gPHBhdGggZD0iTTE5NC43OTgsMTYwLjkwM2MtNC4xODgtMi42NzctOS43NTMtMS40NTQtMTIuNDMyLDIuNzMyYy04LjY5NCwxMy41OTMtMjMuNTAzLDIxLjcwOC0zOS42MTQsMjEuNzA4IGMtMjUuOTA4LDAtNDYuOTg1LTIxLjA3OC00Ni45ODUtNDYuOTg2czIxLjA3Ny00Ni45ODYsNDYuOTg1LTQ2Ljk4NmMxNS42MzMsMCwzMC4yLDcuNzQ3LDM4Ljk2OCwyMC43MjMgYzIuNzgyLDQuMTE3LDguMzc1LDUuMjAxLDEyLjQ5NiwyLjQxOGM0LjExOC0yLjc4Miw1LjIwMS04LjM3NywyLjQxOC0xMi40OTZjLTEyLjExOC0xNy45MzctMzIuMjYyLTI4LjY0NS01My44ODItMjguNjQ1IGMtMzUuODMzLDAtNjQuOTg1LDI5LjE1Mi02NC45ODUsNjQuOTg2czI5LjE1Miw2NC45ODYsNjQuOTg1LDY0Ljk4NmMyMi4yODEsMCw0Mi43NTktMTEuMjE4LDU0Ljc3OC0zMC4wMDkgQzIwMC4yMDgsMTY5LjE0NywxOTguOTg1LDE2My41ODIsMTk0Ljc5OCwxNjAuOTAzeiIvPiA8L2c+IDwvZz4KDTwvc3ZnPg==" height="22">

English | [简体中文][zh-cn-url]

</div>

## Features

- **Fixed Capacity**: Type-level capacity using `generic-array`, all elements live on the stack
- **No Heap Allocation**: Perfect for embedded systems and `no_std` environments
- **Double-Ended**: Efficient push/pop from both ends of the queue
- **Efficient Iteration**: Support for various iterator types including drain and extract_if
- **Rich API**: Similar interface to `std::collections::VecDeque` but with fixed capacity
- **Serde Support**: Optional serialization/deserialization support
- **I/O Support**: `Read` and `Write` trait implementations (with `std` feature)

## Testing & Memory Safety

This crate is rigorously tested for memory safety and correctness using multiple tools:

- **Miri (Tree Borrows)**: All tests pass under Miri with the Tree Borrows aliasing model
- **Miri (Stack Borrows)**: All tests pass under Miri with the Stack Borrows aliasing model
- **Sanitizers**: Tested with AddressSanitizer, MemorySanitizer, and ThreadSanitizer
- **Valgrind**: Memory leak and error detection validated with Valgrind

These extensive checks ensure that all unsafe code is sound and that memory is managed correctly, making this crate safe for use in production environments, including safety-critical systems.

## Implementation Notes

Most of the code in this crate is adapted from Rust's standard library [`VecDeque`](https://doc.rust-lang.org/std/collections/struct.VecDeque.html), modified to work with:

- **Fixed-capacity storage** using `generic-array` instead of heap allocation
- **`const` contexts** where possible, enabling compile-time initialization and evaluation
- **`no_std` environments** without requiring an allocator

The API closely mirrors `std::collections::VecDeque` to provide familiarity, while the implementation is optimized for stack-allocated, fixed-size use cases.

### Why Type-Level Capacity Instead of Const Generics?

While Rust's const generics (`const N: usize`) might seem like a natural choice for specifying capacity, `GenericArrayDeque` uses type-level numbers from the [`typenum`](https://docs.rs/typenum) crate instead. This design choice enables powerful compile-time patterns that aren't possible with const generics, particularly in trait definitions.

**Real-World Example: Syntax Error Tracking**

Consider a trait that defines syntax elements with compile-time known component counts:

```rust
use generic_arraydeque::{GenericArrayDeque, typenum::{U2, U3}};

trait Syntax {
    type Component;
    type ComponentCount: generic_arraydeque::ArrayLength;

    // Each implementation can specify a different capacity at the type level
    fn possible_components() -> &'static GenericArrayDeque<Self::Component, Self::ComponentCount>;
}

// An if-statement has 3 components
struct IfStatement;
impl Syntax for IfStatement {
    type Component = &'static str;
    type ComponentCount = U3;  // Type-level 3

    fn possible_components() -> &'static GenericArrayDeque<Self::Component, U3> {
        // Can be initialized in const context
        static COMPONENTS: GenericArrayDeque<&'static str, U3> = {
            let mut deque = GenericArrayDeque::new();
            // In a const context, populate the deque...
            deque
        };
        &COMPONENTS
    }
}

// A while-loop has 2 components
struct WhileLoop;
impl Syntax for WhileLoop {
    type Component = &'static str;
    type ComponentCount = U2;  // Type-level 2

    fn possible_components() -> &'static GenericArrayDeque<Self::Component, U2> {
        static COMPONENTS: GenericArrayDeque<&'static str, U2> = {
            let mut deque = GenericArrayDeque::new();
            deque
        };
        &COMPONENTS
    }
}
```

**Why This Requires Type-Level Capacity:**

1. **Trait-Level Abstraction**: Each implementor of `Syntax` needs a different capacity, but the capacity must be part of the type system. With `const N: usize`, you can't easily express "each implementation has its own compile-time capacity" in the trait.

2. **Const Context Initialization**: The deques need to be initialized in `const` or `static` contexts. Type-level numbers work seamlessly with `const fn` and generic contexts where the capacity is part of the type.

3. **Zero Runtime Overhead**: The capacity is resolved entirely at compile time as part of type checking. There's no runtime representation of the capacity value.

4. **Future-Proof**: As Rust's const generics mature, there may be migration paths, but for now, type-level numbers provide the necessary expressiveness for these patterns.

This pattern is used in production code for parsing error tracking, where syntax definitions need fixed-capacity collections initialized at compile time with different sizes per syntax element.

## Installation

```toml
[dependencies]
generic-arraydeque = "0.1"
```

## Feature Flags

- `std` (default): Enable standard library support, including `Vec` conversions and I/O traits
- `alloc`: Enable allocator support for `Vec` conversions without full `std`
- `serde`: Enable `Serde` serialization/deserialization support
- `unstable`: Enable unstable features (requires nightly Rust):
  - `pop_front_if` - Conditionally pop from front based on predicate
  - `pop_back_if` - Conditionally pop from back based on predicate
  - `push_back_mut` - Push to back and return mutable reference
  - `push_front_mut` - Push to front and return mutable reference
  - `truncate_front` - Truncate elements from the front
  - `insert_mut` - Insert element and return mutable reference
  - `extend_from_within` - Clone and extend from a range within the deque (requires `T: Clone`)
  - `prepend_from_within` - Clone and prepend from a range within the deque (requires `T: Clone`)
  - `extract_if` - Iterator that extracts elements matching a predicate
- `zeroize`: Enable `Zeroize` support for secure memory clearing
- `faster-hex`: Enable faster hex encoding/decoding

## Why Use `GenericArrayDeque`?

- **Embedded Systems**: No heap allocation required, perfect for memory-constrained environments
- **Real-Time Systems**: Predictable performance without allocator overhead
- **Fixed-Size Buffers**: When you know the maximum capacity at compile-time
- **Type Safety**: Capacity is part of the type, catching errors at compile-time
- **Performance**: Stack allocation is faster than heap allocation

## Usage

### Basic Example

```rust
use generic_arraydeque::{GenericArrayDeque, typenum::U8};

// Create a deque with capacity of 8 elements
let mut deque = GenericArrayDeque::<u32, U8>::new();

// Push elements to the back
deque.push_back(1);
deque.push_back(2);
deque.push_back(3);

// Push elements to the front
deque.push_front(0);

// Pop from both ends
assert_eq!(deque.pop_front(), Some(0));
assert_eq!(deque.pop_back(), Some(3));

assert_eq!(deque.len(), 2);
```

### Working with Capacity

```rust
use generic_arraydeque::{GenericArrayDeque, typenum::U4};

let mut deque = GenericArrayDeque::<i32, U4>::new();

// Try to push - returns overflow value if full
assert_eq!(deque.push_back(1), None);
assert_eq!(deque.push_back(2), None);
assert_eq!(deque.push_back(3), None);
assert_eq!(deque.push_back(4), None);

// Deque is full
assert_eq!(deque.push_back(5), Some(5)); // Returns the value that couldn't be pushed

// Check capacity
assert_eq!(deque.capacity(), 4);
assert_eq!(deque.len(), 4);
assert_eq!(deque.remaining_capacity(), 0);
assert!(deque.is_full());
```

### Creating from Iterators

```rust
use generic_arraydeque::{GenericArrayDeque, typenum::U4};

// From an array
let deque = GenericArrayDeque::<u32, U4>::try_from_array([1, 2, 3, 4]).unwrap();
assert_eq!(deque.len(), 4);

// From an iterator
let deque = GenericArrayDeque::<u32, U4>::try_from_iter(0..3).unwrap();
assert_eq!(deque.into_iter().collect::<Vec<_>>(), vec![0, 1, 2]);

// From an exact size iterator
let deque = GenericArrayDeque::<u32, U4>::try_from_exact_iter(0..4).unwrap();
assert_eq!(deque.len(), 4);
```

### Iteration

```rust
use generic_arraydeque::{GenericArrayDeque, typenum::U4};

let mut deque = GenericArrayDeque::<u32, U4>::try_from_iter(1..=4).unwrap();

// Iterate by reference
for value in &deque {
    println!("{}", value);
}

// Iterate mutably
for value in &mut deque {
    *value *= 2;
}

// Consume into iterator
for value in deque {
    println!("{}", value);
}
```

### Accessing Elements

```rust
use generic_arraydeque::{GenericArrayDeque, typenum::U4};

let mut deque = GenericArrayDeque::<u32, U4>::try_from_iter(10..14).unwrap();

// Index access
assert_eq!(deque[0], 10);
assert_eq!(deque[3], 13);

// Get element
assert_eq!(deque.get(1), Some(&11));
assert_eq!(deque.get(10), None);

// Get front and back
assert_eq!(deque.front(), Some(&10));
assert_eq!(deque.back(), Some(&13));

// Get slices (may be split into two contiguous slices)
let (first, second) = deque.as_slices();
```

## License

`generic-arraydeque` is under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE), [LICENSE-MIT](LICENSE-MIT) for details.

Copyright (c) 2025 Al Liu

Copyright (c) 2010 The Rust Project Developers

[Github-url]: https://github.com/al8n/generic-arraydeque/
[CI-url]: https://github.com/al8n/generic-arraydeque/actions/workflows/ci.yml
[doc-url]: https://docs.rs/generic-arraydeque
[crates-url]: https://crates.io/crates/generic-arraydeque
[codecov-url]: https://app.codecov.io/gh/al8n/generic-arraydeque/
[zh-cn-url]: https://github.com/al8n/generic-arraydeque/tree/main/README-zh_CN.md

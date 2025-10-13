[![Rust](https://github.com/rodrimati1992/typewit_gce/workflows/Rust/badge.svg)](https://github.com/rodrimati1992/typewit_gce/actions)
[![crates-io](https://img.shields.io/crates/v/typewit_gce.svg)](https://crates.io/crates/typewit_gce)
[![api-docs](https://docs.rs/typewit_gce/badge.svg)](https://docs.rs/typewit_gce/*)

For coercing between equal types that use Generic Const Expressions as arguments.

Generic Const Expressions: 
const expresions that use generic parameters from the surrounding item.
To use as generic arguments, this currently requires the [`generic_const_exprs`]
unstable feature.

# Example

Currently (2025-10-13), 
rustc does not allow using a generic `[T; N * M]` where `[T; M * N]` is expected,
so this code:
```rust
#![feature(generic_const_exprs)]

assert_eq!(generate_array::<2>(), [0, 1, 0, 1, 0, 1]);

fn generate_array<const N: usize>() -> [u8; 3 * N] 
where
    [(); N * 3]:
{
    generate_array_b::<N>()
}

fn generate_array_b<const N: usize>() -> [u8; N * 3] {
    std::array::from_fn(|i| (i % N) as u8)
}
```
fails to compile with this error:
```text
error[E0308]: mismatched types
  --> src/lib.rs:23:5
   |
12 |     generate_array_b::<N>()
   |     ^^^^^^^^^^^^^^^^^^^^^^^ expected `3 * N`, found `N * 3`
   |
   = note: expected constant `3 * N`
              found constant `N * 3`
```

Because the compiler can't prove that most equivalent expressions are equal,
this library provides the [`gce_int_eq`] macro for
the purpose of enabling some coercions between equal const-generic types:
```rust
#![feature(generic_const_exprs)]

use typewit_gce::{TypeEq, gce_int_eq};


assert_eq!(generate_array::<2>(), [0, 1, 0, 1, 0, 1]);


fn generate_array<const N: usize>() -> [u8; 3 * N] 
where
    [(); N * 3]:
{
    // a proof that `[u8; N * 3] == [u8; 3 * N]`, 
    // which allows coercing between the two types
    let coercer: TypeEq<[u8; N * 3], [u8; 3 * N]> = 
        TypeEq::NEW.in_array(gce_int_eq!(N * 3, 3 * N));
    
    // coerces `[u8; N * 3]` to the equivalent `[u8; 3 * N]`
    coercer.to_right(generate_array_b::<N>())
}

fn generate_array_b<const N: usize>() -> [u8; N * 3] {
    std::array::from_fn(|i| (i % N) as u8)
}
```
the above code compiles and runs without errors.
Of note is that this does not require additional bounds relative to the original code!


# Reexports

This library reexports all items from `typewit = "1.14.0"`

# No-std support

`typewit_gce` is `#![no_std]`, it can be used anywhere Rust can be used.

# Minimum Supported Rust Version

`typewit_gce` requires Rust nightly due to being made for use with the
[`generic_const_exprs`] feature.


[`generic_const_exprs`
]: https://doc.rust-lang.org/unstable-book/language-features/generic-const-exprs.html
[`gce_int_eq`]: https://docs.rs/typewit_gce/latest/typewit_gce/macro.gce_int_eq.html
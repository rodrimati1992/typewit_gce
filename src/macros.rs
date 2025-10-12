#[cfg(test)]
mod none_delimited_tests;







/// Assert that the arguments are equivalent integer Generic Const Expressions 
/// through a syntax-based analysis.
/// 
/// This macro:
/// - asserts (at macro-expansion time) 
///   the equivalence of its arguments by comparing them in a normalized 
///   representation where algebraically equivalent expressions are considered equal.
/// - returns a [`TypeEq<C<$lhs>, C<$rhs>>`](typewit::TypeEq) 
///   as a proof of the equality of both arguments.
///   `C` stands for the marker type from [`typewit::const_marker`] 
///   that corresponds to the passed-in constants 
///   (e.g.: the [`Usize`](typewit::const_marker::Usize) marker corresponds to `usize`),
/// 
/// [**examples below**](#examples)
/// 
/// # Syntax
/// 
/// This macro supports a subset of valid Rust syntax in each expression:
/// - `+`
/// - `-`(unary and binary)
/// - `*`
/// - `&`(unary): for allowing expressions that borrow, has no effect on equality
/// - `/`: some divisions with polynomials in both the numerator and denominator
///     may not be considered equal to other ways of writing them.
/// - `%`: same limitations as division
/// - `foo()`: function calls are equal if their path and arguments are equal, 
///     the `::<>` (turbofish) syntax isn't allowed.
/// - `( ... )`: all of the allowed syntax can be parenthesized for grouping
/// - `{ ... }`: contains arbitrary syntax that is compared syntactically, 
///    [with some permissive exceptions](#arbitrary-syntax-exceptions).
/// 
/// All subexpressions (except for those in `{...}`) 
/// are normalized so that algebraically equivalent expressions compare equal.
/// 
/// `{ ... }` 
/// <span id="arbitrary-syntax-exceptions">
/// syntax is generally compared syntactically, with these exceptions:
/// </span>
/// 
/// - numeric literals are compared by the value they represent
/// - identifiers are compared without the `r#` prefix
/// 
/// # Limitations
/// 
/// As described above, this macro only operates on its input syntax, 
/// it cannot get the value of passed-in named constants or 
/// the return value of function calls,
/// so its analysis is limited.
/// 
/// This macro also makes these assumption about the arguments: 
/// 1. that the arguments don't expand to different values in different expansions,
///   which is the case with some macros and with `#[track_caller]` const functions.
/// 2. the arithmetic operators (`+`, `-`, `*`, `/`, and `%`) don't cause integer overflow
/// 3. division and remainder don't have a denominator of 0
/// 
/// Assumptions 2 and 3 are currently guaranteed by the compiler.
/// 
/// If those assumptions are broken,
/// this macro causes a const panic when the function that uses this macro is compiled.
/// 
/// # Alternatives
/// 
/// These are some alternatives to using this macro
/// 
/// ### [`typewit::Identity`] trait
/// 
/// The [`Identity`] trait can be used for emulating type equality bounds,
/// 
/// The trait has the advantage that it can be used to prove type equality,
/// but has the disadvantage that it requires the *caller* to prove that 
/// the types are the same.
/// 
/// This macro however, does not require additional bounds to use, 
/// but cannot prove all expressions are equivalent.
/// 
/// <details>
/// <summary> <code>Identity</code> trait example </summary>
/// 
/// This example demonstrates the difference between using [`Identity`] and this macro.
/// 
/// ```rust
/// #![feature(generic_const_exprs)]
/// use typewit_gce::{Identity, TypeEq, gce_int_eq};
/// 
/// const fn swap_add<const A: usize, const B: usize>(array: [u8; A + B]) -> [u8; B + A]
/// where
///     // emulates a `[u8; A + B] == [u8; B + A]` bound
///     [u8; A + B]: Identity<Type = [u8; B + A]>
/// {
///     // performs the `[u8; A + B]` to `[u8; B + A]` coercion
///     Identity::TYPE_EQ.to_right(array)
/// }
/// 
/// // same as the above function
/// const fn swap_add_b<const A: usize, const B: usize>(array: [u8; A + B]) -> [u8; B + A]
/// where
///     // no constraints required!
/// {
///     // performs the `[u8; A + B]` to `[u8; B + A]` coercion
///     TypeEq::NEW.in_array(gce_int_eq!(A + B, B + A)).to_right(array)
/// }
/// ```
/// 
/// </details>
/// 
/// [`Identity`]: typewit::Identity
/// 
/// ### [`const_marker`] types
/// 
/// The [`const_marker`] types are marker types, 
/// each of which is named after the type it has as a const parameter
/// (e.g.: `Usize` has `usize` as its const parameter).
/// 
/// If used in a generic function, these types can be used to const assert
/// that two const expressions are equal, causing a const panic if they aren't.
/// 
/// Using `const_marker` types for const asserting equality of generic constants can 
/// trigger panics in downstream crates if used wrong, so **use with care**.<br>
/// (in constrast, this macro errors on potentially unequal arguments 
/// at the moment the macro is invoked,
/// which doesn't require the function to ever be called)
/// 
/// 
/// <details>
/// <summary> <code>const_marker</code> example </summary>
/// 
/// This example demonstrates the difference between using [`const_marker`] types and this macro.
/// 
/// Using [`const_marker::Usize`](typewit::const_marker::Usize):
/// ```rust,compile_fail
/// #![feature(generic_const_exprs)]
/// use typewit_gce::const_marker::{ConstMarker, CmEquals, Usize};
/// use typewit_gce::TypeEq;
/// 
/// 
/// // compiles these calls successfully
/// assert_eq!(dubious_api::<0, 4>([]), []);
/// assert_eq!(dubious_api::<1, 4>([]), []);
/// 
/// // fails to compile on this call!
/// assert_eq!(dubious_api::<2, 4>([]), [3]);
/// 
/// const fn dubious_api<const A: usize, const B: usize>(array: [u8; A / B]) -> [u8; (A + 2) / B] {
///     // const assert that `A / B` and `(A + 2) / B` are the same
///     // causes a compilation error if this fn is called and they're not the same!
///     let len_eq = const { CmEquals::<Usize<{A / B}>, Usize<{(A + 2) / B}>>::VAL.unwrap_eq() };
///     
///     // performs the `[u8; A / B]` to `[u8; (A + 2) / B]` coercion if reached
///     TypeEq::NEW.in_array(len_eq).to_right(array)
/// }
/// ```
/// The above code errored only when `dubious_api` with unequal types is called,
/// with this error message:
/// ```text
/// error[E0080]: evaluation panicked: called `TypeCmp::unwrap_eq` on a `TypeNe` value
///   --> src/macros.rs:155:26
///    |
/// 21 |     let len_eq = const { CmEquals::<Usize<{A / B}>, Usize<{(A + 2) / B}>>::VAL.unwrap_eq() };
///    |                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ evaluation of `main::_doctest_main_src_macros_rs_137_0::dubious_api::<2, 4>::{constant#2}` failed here
/// 
/// note: erroneous constant encountered
///   --> src/macros.rs:155:18
///    |
/// 21 |     let len_eq = const { CmEquals::<Usize<{A / B}>, Usize<{(A + 2) / B}>>::VAL.unwrap_eq() };
///    |                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
/// 
/// note: the above error was encountered while instantiating `fn dubious_api::<2, 4>`
///   --> src/macros.rs:150:12
///    |
/// 16 | assert_eq!(dubious_api::<2, 4>([]), [3]);
///    |            ^^^^^^^^^^^^^^^^^^^^^^^
/// ```
/// 
/// In contrast, with `gce_int_eq`:
/// ```rust,compile_fail
/// #![feature(generic_const_exprs)]
/// use typewit_gce::{TypeEq, gce_int_eq};
/// 
/// // same API as the above example
/// const fn dubious_api<const A: usize, const B: usize>(array: [u8; A / B]) -> [u8; (A + 2) / B] {
///     // errors because the expressions are not always equal
///     TypeEq::NEW.in_array(gce_int_eq!(A / B, (A + 2) / B)).to_right(array)
/// }
/// ```
/// This errors even if the function isn't called, 
/// because `gce_int_eq` can't prove the two expression are equal,
/// with this error message:
/// ```text
/// error: Cannot prove that the arguments are equal.
///        This is their normalized representation:
///        left: `(A) / (B)`
///        right: `(2 + A) / (B)`
///   --> src/macros.rs:169:26
///    |
/// 12 |     TypeEq::NEW.in_array(gce_int_eq!(A / B, (A + 2) / B)).to_right(array)
///    |                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
///    |
///    = note: this error originates in the macro `gce_int_eq` (in Nightly builds, run with -Z macro-backtrace for more info)
/// ```
/// 
/// </details>
/// 
/// 
/// [`const_marker`]: typewit::const_marker
/// 
/// 
/// # Examples
/// 
/// ### Division
/// 
/// This example 
/// 
/// ```rust
/// #![feature(generic_const_exprs)]
/// use typewit_gce::{TypeEq, gce_int_eq};
/// 
/// assert_eq!(divide_regtangle::<_, 2, 3>([3, 5, 8, 13, 21, 34]), [3, 13]);
/// 
/// 
/// fn divide_regtangle<T, const N: usize, const M: usize>(arr: [T; N * M]) -> [T; N]
/// where
///     // this bounds is required because of the `divide` call
///     [(); N * M / M]:
/// {
///     let divided = divide::<_, {N * M}, M>(arr);
/// 
///     // using `gce_int_eq` here is required to coerce `[T; N * M / M]` to `[T; N]`,
///     // the compiler doesn't yet understand that those are the same type.
///     TypeEq::NEW.in_array(gce_int_eq!(N * M / M, N)).to_right(divided)
/// }
/// 
/// fn divide<T, const N: usize, const D: usize>(arr: [T; N]) -> [T; N / D] {
///     let mut iter = arr.into_iter().step_by(D);
///     std::array::from_fn(|_| iter.next().unwrap())
/// }
/// 
/// ```
/// 
/// ### Const equality
/// 
/// This example demonstrates this macro's support for proving the equality of 
/// expressions that write the constant in twow different ways.
/// 
/// ```rust
/// #![feature(generic_const_exprs)]
/// use typewit_gce::{TypeEq, gce_int_eq};
/// 
/// assert_eq!(remove_two([3, 5]), []);
/// assert_eq!(remove_two([3, 5, 8]), [3]);
/// assert_eq!(remove_two([3, 5, 8, 13]), [3, 5]);
/// 
/// 
/// fn remove_two<T, const N: usize>(arr: [T; N]) -> [T; N - 2] 
/// where 
///     // these bounds are required because of the `pop_array` calls
///     [(); N - 1]:,
///     [(); N - 1 - 1]:,
/// {
///     let (arr, _) = pop_array::<_, {N}>(arr);
///     let (arr, _) = pop_array::<_, {N - 1}>(arr);
///     
///     // using `gce_int_eq` here is required to coerce `[T; N - 1 - 1]` to `[T; N - 2]`,
///     // the compiler doesn't yet understand that those are the same type.
///     TypeEq::NEW.in_array(gce_int_eq!(N - 1 - 1, N - 2)).to_right(arr)
/// }
/// 
/// fn pop_array<T, const N: usize>(arr: [T; N]) -> ([T; N - 1], T) {
///     let mut iter = arr.into_iter();
///     (std::array::from_fn(|_| iter.next().unwrap()), iter.next().unwrap())
/// }
/// ```
/// 
/// ### Other coercions
/// 
/// This example showcases some more types that the compiler does not yet consider equal, 
/// which this crate does.
/// 
/// ```rust
/// #![feature(generic_const_exprs)]
/// use typewit_gce::{TypeEq, gce_int_eq};
/// 
/// 
/// assert_eq!(commutative_add::<3, 2>([3, 5, 8, 13, 21]), [3, 5, 8, 13, 21]);
/// 
/// const fn commutative_add<const N: usize, const M: usize>(arr: [u8; N + M]) -> [u8; M + N] {
///     TypeEq::NEW.in_array(gce_int_eq!(N + M, M + N)).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(sub_cancels_out::<3, 1>([3]), [3]);
/// assert_eq!(sub_cancels_out::<3, 2>([3, 5]), [3, 5]);
/// assert_eq!(sub_cancels_out::<5, 2>([3, 5]), [3, 5]);
/// assert_eq!(sub_cancels_out::<8, 2>([3, 5]), [3, 5]);
/// 
/// const fn sub_cancels_out<const N: usize, const M: usize>(arr: [u8; N - N + M]) -> [u8; M] {
///     TypeEq::NEW.in_array(gce_int_eq!(N - N + M, M)).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(commutative_mul::<3, 2>([3, 5, 8, 13, 21, 34]), [3, 5, 8, 13, 21, 34]);
/// 
/// const fn commutative_mul<const N: usize, const M: usize>(arr: [u8; N * M]) -> [u8; M * N] {
///     TypeEq::NEW.in_array(gce_int_eq!(N * M, M * N)).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(distributive_mul::<2, 1>([3, 5, 8, 13]), [3, 5, 8, 13]);
/// 
/// const fn distributive_mul<const N: usize, const M: usize>(
///     arr: [u8; N * (1 + M)]
/// ) -> [u8; N + M * N] {
///     TypeEq::NEW.in_array(gce_int_eq!(N * (1 + M), N + M * N)).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(simplify_div::<1>([3, 5, 8]), [3, 5, 8]);
/// assert_eq!(simplify_div::<2>([3]), [3]);
/// assert_eq!(simplify_div::<3>([]), []);
/// assert_eq!(simplify_div::<4>([]), []);
/// 
/// const fn simplify_div<const N: usize>(
///     arr: [u8; (3 * N + 6) / (3 * N * N)]
/// ) -> [u8; (N + 2) / (N * N)] {
///     let len_te = gce_int_eq!((3 * N + 6) / (3 * N * N), (N + 2) / (N * N));
///     TypeEq::NEW.in_array(len_te).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(extract_div::<1>([3, 5]), [3, 5]);
/// assert_eq!(extract_div::<2>([3]), [3]);
/// assert_eq!(extract_div::<3>([3]), [3]);
/// 
/// const fn extract_div<const N: usize>(arr: [u8; (N + 1) / N]) -> [u8; 1 + 1 / N] {
///     TypeEq::NEW.in_array(gce_int_eq!((N + 1) / N, 1 + 1 / N)).to_right(arr)
/// }
/// 
/// ```
/// 
#[macro_export]
macro_rules! gce_int_eq {
    ($lhs:expr, $rhs:expr $(, $ty:ty)? $(,)?) => {{
        $crate::__::assert_equal!{($crate) $lhs , $rhs}

        let mut marker = $crate::__GceIntEqHelper::NEW;
        if false {
            $crate::__gce_int_eq__infer_if_no_type!{$($ty)?, marker, $lhs, $rhs};
            marker.infer_from_return()
        } else {
            $crate::__::call_equality_proof_fn!(marker $lhs $rhs)
        }
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __gce_int_eq__infer_if_no_type {
    (, $marker:ident, $lhs:expr, $rhs:expr) => { 
        $marker = $marker.infer_from_arg(&$lhs, &$rhs);
    };
    ($ty:ty, $marker:ident, $lhs:expr, $rhs:expr) => {
        $marker = $crate::__GceIntEqHelper::<$ty, _, _>::NEW
    };
}
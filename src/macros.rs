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
/// # Syntax
/// 
/// This macro supports a subset of valid Rust syntax:
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
/// fn commutative_add<const N: usize, const M: usize>(arr: [u8; N + M]) -> [u8; M + N] {
///     TypeEq::NEW.in_array(gce_int_eq!(N + M, M + N)).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(sub_cancels_out::<3, 1>([3]), [3]);
/// assert_eq!(sub_cancels_out::<3, 2>([3, 5]), [3, 5]);
/// assert_eq!(sub_cancels_out::<5, 2>([3, 5]), [3, 5]);
/// assert_eq!(sub_cancels_out::<8, 2>([3, 5]), [3, 5]);
/// 
/// fn sub_cancels_out<const N: usize, const M: usize>(arr: [u8; N - N + M]) -> [u8; M] {
///     TypeEq::NEW.in_array(gce_int_eq!(N - N + M, M)).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(commutative_mul::<3, 2>([3, 5, 8, 13, 21, 34]), [3, 5, 8, 13, 21, 34]);
/// 
/// fn commutative_mul<const N: usize, const M: usize>(arr: [u8; N * M]) -> [u8; M * N] {
///     TypeEq::NEW.in_array(gce_int_eq!(N * M, M * N)).to_right(arr)
/// }
/// 
/// 
/// assert_eq!(distributive_mul::<2, 1>([3, 5, 8, 13]), [3, 5, 8, 13]);
/// 
/// fn distributive_mul<const N: usize, const M: usize>(
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
/// fn simplify_div<const N: usize>(
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
/// fn extract_div<const N: usize>(arr: [u8; (N + 1) / N]) -> [u8; 1 + 1 / N] {
///     TypeEq::NEW.in_array(gce_int_eq!((N + 1) / N, 1 + 1 / N)).to_right(arr)
/// }
/// 
/// ```
/// 
#[macro_export]
macro_rules! gce_int_eq {
    ($lhs:expr, $rhs:expr $(, $ty:ty)? $(,)?) => {{
        $crate::__::assert_equal!{($crate) $lhs , $rhs}

        let marker;
        if false {
            marker = $crate::__gce_int_eq__infer_if_no_type!{$($ty)?, $lhs, $rhs};
            marker.infer_from_return()
        } else {
            marker = $crate::__::__ConstMarkerFactory::NEW;
            $crate::__::call_equality_proof_fn!(marker $lhs $rhs)
        }
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __gce_int_eq__infer_if_no_type {
    (, $lhs:expr, $rhs:expr) => { 
        $crate::__::__ConstMarkerFactory::new(&$lhs, &$rhs) 
    };
    ($ty:ty, $lhs:expr, $rhs:expr) => {
        $crate::__::__ConstMarkerFactory::<$ty>::NEW
    };
}
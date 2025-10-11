
/// Assert that the `$lhs` and `$rhs` are equivalent Generic Const Expressions 
/// through a syntax-based analysis.
/// 
/// This macro asserts the equivalence of its arguments by parsing the arguments,
/// then comparing them in a normalized representation where 
/// algebraically equivalent expressions are considered equal.
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
/// 
/// <div id="arbitrary-syntax-exceptions"></div>
/// `{ ... }` syntax is generally compared syntactically, with these exceptions:
/// - numeric literals are compared by the value they represent
/// - identifiers are compared without the `r#` prefix
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
/// 
/// 
/// 
/// 
/// 
/// 
/// 
/// 
/// 
/// 
/// 
/// 
/// 
#[macro_export]
macro_rules! gce_int_eq{
    ($lhs:expr, $rhs:expr $(,)?) => {{
        $crate::__::assert_equal!{($crate) $lhs , $rhs}

        let marker;
        if false {
            marker = $crate::__::__ConstMarkerFactory::new(&$lhs, &$rhs);
            marker.infer_from_return()
        } else {
            marker = $crate::__::__ConstMarkerFactory::NEW;
            marker.get_equality_proof::<{$lhs}, {$rhs}>()
        }
    }};
    ($lhs:expr, $rhs:expr, $type:ty $(,)?) => {{
        $crate::__::assert_equal!{($crate) $lhs , $rhs}

        let marker = $crate::__::__ConstMarkerFactory::<$type>::NEW;
        if false {
            marker.infer_from_return()
        } else {
            marker.get_equality_proof::<{$lhs}, {$rhs}>()
        }
    }};
}
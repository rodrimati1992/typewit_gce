use crate::SimplifyFraction;

use super::{normal_tests::parse, Polynomial};

#[track_caller]
fn asse_eq(s: &str) {
    // the rhs of the equal sign doesn't reduce fractions beyond 
    // normalizing the numerator and denominator individually
    let (l, r) = parse(s, SimplifyFraction::No).unwrap();

    assert_eq!(l, r, "{s}");
}

#[track_caller]
fn asse_ne(s: &str) {
    let (l, r) = parse(s, SimplifyFraction::No).unwrap();

    assert_ne!(l, r, "{s}");
}


// ensuring that `asse_eq` and `asse_ne` don't reduce the rhs
#[test]
fn test_asse_of_rem_doesnt_reduce_the_rhs() {
    asse_eq("6 % 3 = 0");

    asse_ne("6 % 3 = 6 % 3");
    asse_ne("6 % 3 = 3 % 2");
}

#[test]
fn test_asse_of_div_doesnt_reduce_the_rhs() {
    asse_eq("6 / 3 = 2");

    asse_ne("6 / 3 = 6 / 3");
}


#[test]
fn test_rem_constants() {
    asse_eq("0 % 3 = 0");
    asse_eq("1 % 3 = 1");
    asse_eq("2 % 3 = 2");
    asse_eq("3 % 3 = 0");
    asse_eq("4 % 3 = 1");
}

#[test]
fn test_rem_single_numerator_term() {
    asse_eq("x * 2 % 3 = 2 * x % 3");
    asse_eq("y * (x * 2 % 3) = 2 * x % 3 * y");

    asse_eq("x * 3 % 3 = 0");
    
    asse_ne("x % 3 = x % 2");
    asse_ne("x % y = x % z");
    asse_ne("x % 3 = 3");
    asse_ne("x % 3 = x");
}

#[test]
fn test_rem_poly_numerator() {
    asse_eq("(x * 3 + 3) % 3 = 0");
    asse_eq("(x * 3 + 2) % 3 = 2");
    asse_eq("(x * 3 + 1) % 3 = 1");

    asse_eq("(x * 3 + 3) % x = 3 % x");
    asse_eq("(x * 3 + 2) % x = 2 % x");
    asse_eq("(x * 3 + 1) % x = 1 % x");

    asse_eq("(x * y + 3) % x = 3 % x");
    asse_eq("(x * y + 2) % x = 2 % x");
    asse_eq("(x * y + 1) % x = 1 % x");
}


#[test]
fn test_div_unequal_denoms() {
    asse_ne("x / 3 = x / 2");
    asse_ne("x / y = x / z");
    asse_ne("x / y = 1 / 1");
    asse_ne("x / y = 1 / y");
}

#[test]
fn test_div_normalization_of_numerator_on_its_own() {
    asse_eq("(x + x) / 3 = 2 * x / 3");
    asse_eq("(-x + 2*x) / 3 = x / 3");
}

#[test]
fn test_div_normalization_of_denominator_on_its_own() {
    asse_eq("x / (5 - 2) = x / 3");
    asse_eq("x / (2*y - y) = x / y");
}

#[test]
fn test_div_commutative() {
    asse_eq("x * 2 / 3 = 2 * x / 3");
    asse_eq("x * 2 / 3 = 2 * x / 3");

    asse_eq("x * 2 / 3 = 2 * x / 3");
    asse_eq("x * 2 / -3 = 2 * x / (-3)");
    asse_eq("x * 2 / 3 * y = y * (2 * x / 3)");
}

#[test]
fn test_div_simplify_one_term_numerator_to_zero() {
    asse_eq("0 / 3 = 0");
    asse_eq("1 / 3 = 0");
    asse_eq("2 / 3 = 0");
    asse_eq("0 / 3*x = 0");
    asse_eq("1 / 3*x = 0");
    asse_eq("2 / 3*x = 0");
    asse_eq("2 / 3*x*foo(y) = 0");
    
    asse_ne("2 / (3*x*foo(y) + 1) = 0");
}

#[test]
fn test_div_simplify_one_term_numerator() {
    asse_eq("16 / 3 = 5");
    asse_eq("7 / 3 = 2");
    asse_eq("3 / 3 = 1");
    
    asse_eq("x / -x = -1");
    asse_eq("x / -1 = -x");
    asse_eq("10 * x / -2 = -5*x");
    asse_eq("-10 * 3 * x / -2 = 15*x");
    asse_eq("2 * x / -1 = - 2 * x");
    asse_eq("-2 * x / 2 = -x");

    // integer division loses the fractional part, so (x / 3) * 3 != x
    asse_ne("x / 3 * 3 = x");
    asse_ne("y / x = y");
}

#[test]
fn test_div_simplify_polynomial_numerator() {
    asse_eq("(3 * (y + 2 * x + 1 - 1)) / x = 3 * y / x + 6");
    
    asse_eq("(3 * (x + y)) / x = 3 + 3 * y / x");
    asse_eq("(12 * (x + y)) / (3 * x) = 4 + 4 * y / x");

    // polynomial terms that divide with non-0 remainder can't be moved out of the fraction
    asse_ne("(x + 1) / (2 * x) = (1 / 2) + (1 / (2 * x))");
    
    asse_eq("(x + 1) / x = 1 + (1 / x)");
    asse_eq("(x + y) / x = 1 + (y / x)");
    asse_eq("(x * x + y) / x = x + (y / x)");
    asse_eq("(x * x * x + y) / x = x * x + (y / x)");
    asse_eq("(x * x * x + y) / x = x * x + (y / x)");
    asse_eq("(x * (x + y)) / x = x + y");

    asse_ne("(x + y) / x = x + y");
    asse_ne("(x * (x + y)) / (x + 1) = x + y");
}

#[test]
fn test_div_simplify_polynomial_denom() {
    asse_eq("2 * (x + 1) / (x + 2) = 2 * (x + 1) / (x + 2)");
    
    // this doesn't work yet
    asse_ne("2 * (x + 1) / (x + 1) = 2");
}


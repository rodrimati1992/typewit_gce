use super::{
    normal_tests::{asse_eq, asse_ne, polynomial_1term, polynomial_1var, parse},
    Varlike as VL,
    FunctionCall as FC,
    Polynomial,
};

// ensuring that `asse_eq` and `asse_ne` don't reduce the rhs
#[test]
fn test_asse_of_rem_doesnt_reduce_the_rhs() {
    asse_eq("", "6 % 3 = 0");

    assert_eq!(
        parse("6 % 3 = 6 % 3").unwrap(),
        (
            Polynomial::zero(),
            polynomial_1var(
                VL::FunctionCall(FC::Rem(
                    polynomial_1term(vec![], 6).into(),
                    polynomial_1term(vec![], 3).into(),
                ))
            )
        )
    );

    assert_eq!(
        parse("6 % 3 = 3 % 2").unwrap(),
        (
            Polynomial::zero(),
            polynomial_1var(
                VL::FunctionCall(FC::Rem(
                    polynomial_1term(vec![], 3).into(),
                    polynomial_1term(vec![], 2).into(),
                ))
            )
        )
    );
}

#[test]
fn test_asse_of_div_doesnt_reduce_the_rhs() {
    asse_eq("", "6 / 3 = 2");

    assert_eq!(
        parse("6 / 3 = 6 / 3").unwrap(),
        (
            polynomial_1term(vec![], 2),
            polynomial_1var(
                VL::FunctionCall(FC::Div(
                    polynomial_1term(vec![], 6).into(),
                    polynomial_1term(vec![], 3).into(),
                ))
            )
        )
    );
}


#[test]
fn test_rem_constants() {
    asse_eq("", "0 % 3 = 0");
    asse_eq("", "1 % 3 = 1");
    asse_eq("", "2 % 3 = 2");
    asse_eq("", "3 % 3 = 0");
    asse_eq("", "4 % 3 = 1");
}

#[test]
fn test_rem_sign() {
    asse_eq("x,y", "x % y   =   (x % y)");
    asse_eq("x,y", "-x % y  = - (x % y)");
    asse_eq("x,y", "x % -y  =   (x % y)");
    asse_eq("x,y", "-x % -y = - (x % y)");
}

#[test]
fn test_rem_single_numerator_term() {
    asse_eq("x", "x * 2 % 3 = 2 * x % 3");
    asse_eq("x,y", "y * (x * 2 % 3) = 2 * x % 3 * y");

    asse_eq("x", "x * 3 % 3 = 0");
    
    asse_ne("x", "x % 3 = x % 2");
    asse_ne("x,y,z", "x % y = x % z");
    asse_ne("x", "x % 3 = 3");
    asse_ne("x", "x % 3 = x");
}

#[test]
fn test_rem_poly_numerator() {
    asse_eq("x", "(x * 3 + 3) % 3 = 0");
    asse_eq("x", "(x * 3 + 2) % 3 = 2");
    asse_eq("x", "(x * 3 + 1) % 3 = 1");

    asse_eq("x", "(x * 3 + 3) % x = 3 % x");
    asse_eq("x", "(x * 3 + 2) % x = 2 % x");
    asse_eq("x", "(x * 3 + 1) % x = 1 % x");

    asse_eq("x,y", "(x * y + 3) % x = 3 % x");
    asse_eq("x,y", "(x * y + 2) % x = 2 % x");
    asse_eq("x,y", "(x * y + 1) % x = 1 % x");
}


#[test]
fn test_div_sign() {
    asse_eq("x,y", "x / y   =   (x / y)");
    asse_eq("x,y", "-x / y  = - (x / y)");
    asse_eq("x,y", "x / -y  = - (x / y)");
    asse_eq("x,y", "-x / -y =   (x / y)");
}

#[test]
fn test_div_unequal_denoms() {
    asse_ne("x", "x / 3 = x / 2");
    asse_ne("x,y,z", "x / y = x / z");
    asse_ne("x,y", "x / y = 1 / 1");
    asse_ne("x,y", "x / y = 1 / y");
}

#[test]
fn test_div_normalization_of_numerator_on_its_own() {
    asse_eq("x", "(x + x) / 3 = 2 * x / 3");
    asse_eq("x", "(-x + 2*x) / 3 = x / 3");
}

#[test]
fn test_div_normalization_of_denominator_on_its_own() {
    asse_eq("x", "x / (5 - 2) = x / 3");
    asse_eq("x,y", "x / (2*y - y) = x / y");
}

#[test]
fn test_div_commutative() {
    asse_eq("x", "x * 2 / 3 = 2 * x / 3");
    asse_eq("x", "x * 2 / 3 = 2 * x / 3");

    asse_eq("x", "x * 2 / 3 = 2 * x / 3");
    asse_eq("x", "x * 2 / -3 = - (2 * x / 3)");
    asse_eq("x,y", "x * 2 / 3 * y = y * (2 * x / 3)");
}

#[test]
fn test_div_nested() {
    asse_eq("X,Y,Z,W", "1 / X * Y / Z / W = ((Y * (1 / X)) / Z) / W");
}

#[test]
fn test_div_simplify_one_term_numerator_to_zero() {
    asse_eq("", "0 / 3 = 0");
    asse_eq("", "1 / 3 = 0");
    asse_eq("", "2 / 3 = 0");
    asse_eq("x", "0 / 3*x = 0");
    asse_eq("x", "1 / 3*x = 0");
    asse_eq("x", "2 / 3*x = 0");
    asse_eq("x,y", "2 / 3*x*foo(y) = 0");
    
    asse_ne("x,y,foo", "2 / (3*x*foo(y) + 1) = 0");
}

#[test]
fn test_div_simplify_one_term_numerator() {
    asse_eq("", "16 / 3 = 5");
    asse_eq("", "7 / 3 = 2");
    asse_eq("", "3 / 3 = 1");
    
    asse_eq("x", "x / -x = -1");
    asse_eq("x", "x / -1 = -x");
    asse_eq("x", "10 * x / -2 = -5*x");
    asse_eq("x", "-10 * 3 * x / -2 = 15*x");
    asse_eq("x", "2 * x / -1 = - 2 * x");
    asse_eq("x", "-2 * x / 2 = -x");

    // integer division loses the fractional part, so (x / 3) * 3 != x
    asse_ne("x", "x / 3 * 3 = x");
    asse_ne("x,y", "y / x = y");
}

#[test]
fn test_div_simplify_polynomial_numerator() {
    asse_eq("x,y", "(3 * (y + 2 * x + 1 - 1)) / x = 3 * y / x + 6");
    
    asse_eq("x,y", "(3 * (x + y)) / x = 3 + 3 * y / x");
    asse_eq("x,y", "(12 * (x + y)) / (3 * x) = 4 + 4 * y / x");

    // polynomial terms that divide with non-0 remainder can't be moved out of the fraction
    asse_ne("x", "(x + 1) / (2 * x) = (1 / 2) + (1 / (2 * x))");
    
    asse_eq("x", "(x + 1) / x = 1 + (1 / x)");
    asse_eq("x,y", "(x + y) / x = 1 + (y / x)");
    asse_eq("x,y", "(x * x + y) / x = x + (y / x)");
    asse_eq("x,y", "(x * x * x + y) / x = x * x + (y / x)");
    asse_eq("x,y", "(x * x * x + y) / x = x * x + (y / x)");
    asse_eq("x,y", "(x * (x + y)) / x = x + y");

    asse_ne("x,y", "(x + y) / x = x + y");
    asse_ne("x,y", "(x * (x + y)) / (x + 1) = x + y");
}

#[test]
fn test_div_simplify_polynomial_denom() {
    asse_eq("x", "2 * (x + 1) / (x + 2) = 2 * (x + 1) / (x + 2)");
    
    // this doesn't work yet
    asse_ne("x", "2 * (x + 1) / (x + 1) = 2");
}


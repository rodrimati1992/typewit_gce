use crate::error::Error;
use crate::utils::CrateToken;

use super::Polynomial;

#[track_caller]
fn parse(s: &str) -> Result<(Polynomial, Polynomial), Error> {
    let input_tokens: crate::used_proc_macro::TokenStream = s.parse().unwrap();
    let iter = &mut input_tokens.into_iter().peekable();

    let crate_token = CrateToken {
        krate: "crate".parse().unwrap()
    };

    crate::__parse_polynomials(&crate_token, iter).map_err(|(_, e)| e)
}

#[track_caller]
fn asse_eq(s: &str) {
    let (l, r) = parse(s).unwrap();

    assert_eq!(l, r, "{s}");
}

#[track_caller]
fn asse_ne(s: &str) {
    let (l, r) = parse(s).unwrap();

    assert_ne!(l, r, "{s}");
}


#[test]
fn test_simples() {
    asse_eq("x = x");
    asse_eq("1 = 1");
    asse_eq("0 = 0");
    asse_eq("-1 = -1");
    asse_eq("f() = f()");
}

#[test]
fn test_identities() {
    asse_eq("x + 0 = x");
    asse_eq("x - 0 = x");
    asse_eq("x + n * 0 = x");
    asse_eq("x + n % 1 = x");
    asse_eq("x / 1 = x");
    asse_eq("x - x = 0");
}

#[test]
fn test_commutative() {
    asse_eq("x + n = n + x");
    asse_eq("x * n = n * x");
    asse_eq("x - n = - n + x");
    asse_eq("x + f(3) = f(3) + x");
}

#[test]
fn test_noncommutative() {
    asse_ne("x - n = n - x");
}

#[test]
fn test_rem() {
    asse_eq("x * 2 % 3 = 2 * x % 3");
    asse_eq("y * (x * 2 % 3) = 2 * x % 3 * y");
    
    asse_ne("x * 3 % 3 = 0");
}

#[test]
fn test_div() {
    asse_eq("x * 2 / 3 = 2 * x / 3");
    asse_eq("x * 2 / -3 = 2 * x / (-3)");
    asse_eq("x * 2 / 3 * y = y * (2 * x / 3)");
    
    asse_ne("3 / 3 = 1");
    asse_ne("x / 3 * 3 = x");
    asse_ne("x / -1 = -x");
}

#[test]
fn test_function() {
    asse_eq("f(2 * 3, x + y) + 1 = 1 + f(1 * 6, y + x)");
    
    asse_eq("f(2 * 3, x + y) * 0 = 0");
    
    asse_ne("f() = g()");
    asse_ne("f(1) = f(1 + 1)");
    asse_ne("f(1) = f(1, 1)");
}

#[test]
fn test_function_path() {
    asse_eq("i32::wrapping_add(2, 3) = i32::wrapping_add(2, 3)");
    asse_eq("::foo::bar(2, 3) = ::foo::bar(2, 3)");
    
    asse_ne("::foo::bar(2, 3) = foo::bar(2, 3)");
}

#[test]
fn test_distributive_fn() {
    asse_eq("(x + 1) * f(y) = x * f(y) + f(y)");
    asse_eq("(f(y) + 1) * f(y) = f(y) * f(y) + f(y)");
    asse_eq("(-f(y) + 0) * -f(y) = f(y) * f(y)");
}

#[test]
fn test_distributive_single() {
    asse_eq("(x + 1) * 1 = x + 1");
    asse_eq("(x + 1) * -1 = -x - 1");
    asse_eq("(x + 1) * 2 = 2 * x + 2");
    asse_eq("(x + 1) * -2 = -2 * x - 2");
    asse_eq("-(x + 1) * -2 = 2 * x + 2");
    asse_eq("(x + 1) * x = x * x + x");
}

#[test]
fn test_distributive_double() {
    asse_eq("(x + 1) * (x + 1) = x * x + 2 * x + 1");
    
    asse_eq("(x - 1) * (x - 1) = x * x - 2 * x + 1");
}

#[test]
fn test_distributive_double_multivariate() {
    asse_eq("(x + y) * (x + 1) = x * x + x + y * x + y");

    asse_eq("(x + y) * (3 * z + w) = 3 * x * z + x * w + 3 * y * z + y * w");
    asse_eq("(x + y) * (3 * z + w) = 3 * z * (x + y) + w * (x + y)");
}

#[test]
fn test_distributive_triple() {
    asse_eq("(x + 1) * (x + 1) * (x + 1) = x * x * x + 3 * x * x + 3 * x + 1");
    
    asse_eq("(x - 1) * (x - 1) * (x - 1) = x * x * x - 3 * x * x + 3 * x - 1");
}




































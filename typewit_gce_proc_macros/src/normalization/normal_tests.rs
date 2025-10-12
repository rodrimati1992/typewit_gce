use crate::{
    error::Error,
    utils::CrateToken,
    SimplifyFraction,
};

use super::{Polynomial, Varlike};

use num_bigint::BigInt;

use itertools::Itertools;


pub(super) fn polynomial_1term(vars: Vec<(Varlike, u128)>, coeff: i128) -> Polynomial {
    make_polynomial(vec![(vars, coeff.into())])
}

pub(super) fn polynomial_1var(varlike: Varlike) -> Polynomial {
    make_polynomial(vec![(vec![(varlike, 1u8.into())], 1u8.into())])
}

pub(super) fn make_polynomial(vect: Vec<(Vec<(Varlike, u128)>, i128)>) -> Polynomial {
    Polynomial {
        terms: vect
            .into_iter()
            .map(|(vars, coeff)| (
                vars.into_iter().map(|(var, pow)| (var, pow.into())).collect(), 
                coeff.into(),
            ))
            .collect()
    }
}


#[track_caller]
pub(super) fn parse(
    s: &str, 
) -> Result<(Polynomial, Polynomial), Error> {
    let input_tokens: crate::used_proc_macro::TokenStream = s.parse().unwrap();
    let iter = &mut input_tokens.into_iter().peekable();

    let crate_token = CrateToken {
        krate: "crate".parse().unwrap()
    };

    crate::__parse_polynomials(&crate_token, SimplifyFraction::No, iter).map_err(|(_, e)| e)
}

#[track_caller]
pub(super) fn run_interpreter(
    vars: &[&str], 
    lhs: &Polynomial, 
    rhs: &Polynomial, 
    the_assert: &mut dyn FnMut(Option<BigInt>, Option<BigInt>)
)  {
    let mut map = std::collections::HashMap::new();

    if vars.is_empty() {
        the_assert(
            super::test_interpreter::interpret_poly(lhs, &map).unwrap(),
            super::test_interpreter::interpret_poly(rhs, &map).unwrap(),
        )
    } else {        
        vars.iter()
            .map(|var| {
                (-7i8..7).map(move|x| {
                    (var.to_string(), BigInt::from(x))
                })
            })
            .multi_cartesian_product()
            .for_each(|vars_with_vals| {
                map.clear();
                map.extend(vars_with_vals);

                the_assert(
                    super::test_interpreter::interpret_poly(lhs, &map).unwrap(),
                    super::test_interpreter::interpret_poly(rhs, &map).unwrap(),
                )
            })
    }
}

#[track_caller]
pub(super) fn asse_eq(vars: &str, s: &str) {
    let (l, r) = parse(s).unwrap();

    let vars = vars.split(',').map(|x| x.trim()).collect::<Vec<_>>();

    assert_eq!(l, r, "{s}");

    run_interpreter(&vars, &l, &r, &mut |l_val, r_val| {
        assert_eq!(l_val, r_val, "{s}");
    });
}

#[track_caller]
pub(super) fn asse_ne(vars: &str, s: &str) {
    let (l, r) = parse(s).unwrap();

    let vars = vars.split(',').map(|x| x.trim()).collect::<Vec<_>>();

    assert_ne!(l, r, "{s}");

    let mut found_ne = false;
    run_interpreter(&vars, &l, &r, &mut |l_val, r_val| {
        found_ne = found_ne || l_val != r_val;
    });
        
    assert!(found_ne, "could not find counter-example: {l:?}\n{r:?}");
}

#[test]
fn test_simples() {
    asse_eq("x", "x = x");
    asse_ne("x,y", "x = y");

    asse_eq("", "1 = 1");
    asse_eq("", "0 = 0");
    asse_eq("", "-1 = -1");
    asse_ne("", "1 = 2");
    asse_ne("", "0 = 1");
    asse_ne("", "-1 = 1");
    
    asse_eq("f", "f() = f()");
    asse_ne("f,g", "f() = g()");
}

#[test]
fn test_identities() {
    asse_eq("x", "x + 0 = x");
    asse_eq("x", "x - 0 = x");
    asse_eq("x", "x + n * 0 = x");
    asse_eq("x", "x + n % 1 = x");
    asse_eq("x", "x / 1 = x");
    asse_eq("x", "x - x = 0");
}

#[test]
fn test_commutative() {
    asse_eq("x,n", "x + n = n + x");
    asse_eq("x,n", "x * n = n * x");
    asse_eq("x,n", "x - n = - n + x");
    asse_eq("x,n,f", "x + f(3) = f(3) + x");
}

#[test]
fn test_noncommutative() {
    asse_ne("x,n", "x - n = n - x");
}

#[test]
fn test_function() {
    asse_eq("x,y,f", "f(2 * 3, x + y) + 1 = 1 + f(1 * 6, y + x)");
    
    asse_eq("x,y,f", "f(2 * 3, x + y) * 0 = 0");
    
    asse_ne("f,g", "f() = g()");
    asse_ne("f", "f(1) = f(1 + 1)");
    asse_ne("f", "f(1) = f(1, 1)");
}

#[test]
fn test_function_path() {
    asse_eq("i32::wrapping_add", "i32::wrapping_add(2, 3) = i32::wrapping_add(2, 3)");
    asse_eq("::foo::bar", "::foo::bar(2, 3) = ::foo::bar(2, 3)");
    
    asse_ne("::foo::bar, foo::bar", "::foo::bar(2, 3) = foo::bar(2, 3)");
}

#[test]
fn test_distributive_fn() {
    asse_eq("x,y,f", "(x + 1) * f(y) = x * f(y) + f(y)");
    asse_eq("y,f", "(f(y) + 1) * f(y) = f(y) * f(y) + f(y)");
    asse_eq("y,f", "(-f(y) + 0) * -f(y) = f(y) * f(y)");
    
    asse_ne("y,f", "(f(y) + 0) * f(y) = f(y) * 1");
}

#[test]
fn test_distributive_single() {
    asse_eq("x", "(x + 1) * 1 = x + 1");
    asse_eq("x", "(x + 1) * -1 = -x - 1");
    asse_eq("x", "(x + 1) * 2 = 2 * x + 2");
    asse_eq("x", "(x + 1) * -2 = -2 * x - 2");
    asse_eq("x", "-(x + 1) * -2 = 2 * x + 2");
    asse_eq("x", "(x + 1) * x = x * x + x");
    
    asse_ne("x", "(x + 1) * x = x * x + 1");
}

#[test]
fn test_distributive_double() {
    asse_eq("x", "(x + 1) * (x + 1) = x * x + 2 * x + 1");
    
    asse_eq("x", "(x - 1) * (x - 1) = x * x - 2 * x + 1");
    
    asse_ne("x", "(x - 1) * (x - 1) = x * x + 2 * x + 1");
}

#[test]
fn test_distributive_double_multivariate() {
    asse_eq("x,y", "(x + y) * (x + 1) = x * x + x + y * x + y");

    asse_eq("x,y,z,w", "(x + y) * (3 * z + w) = 3 * x * z + x * w + 3 * y * z + y * w");
    asse_eq("x,y,z,w", "(x + y) * (3 * z + w) = 3 * z * (x + y) + w * (x + y)");

    asse_ne("x,y,z,w", "(x + y) * (3 * z + w) = 3 * z * (x + y) + w * (x + 1)");

}

#[test]
fn test_distributive_triple() {
    asse_eq("x", "(x + 1) * (x + 1) * (x + 1) = x * x * x + 3 * x * x + 3 * x + 1");
    
    asse_eq("x", "(x - 1) * (x - 1) * (x - 1) = x * x * x - 3 * x * x + 3 * x - 1");
    
    asse_ne("x", "(x - 1) * (x - 1) * (x - 1) = x * x * x + 3 * x * x + 3 * x + 1");
}


#[test]
fn test_unevaled_lits() {
    asse_eq("", "{ 0i8 } = { 0u8 }");
    asse_eq("", "{ 0_i8 } = { 0_u8 }");
    asse_eq("", "{ -1_i8 } = { -1_isize }");

    asse_eq("", "{ 10.wrapping_add(0b111) } = { 0xA.wrapping_add(7) }");
    asse_eq("", "{ 0o12.wrapping_add(0b111) } = { 10.wrapping_add(7) }");
    
    asse_ne("", "{ 10 } = { 11 }");
    asse_ne("", "{ \"foo\" } = { b\"foo\" }");
}

#[test]
fn test_unevaled_char_lits() {
    asse_eq("", r#"{ 'a' } = { 'a' }"#);
    asse_eq("", r#"{ '\0' } = { '\0' }"#);

    asse_ne("", r#"{ 'a' } = { b'a' }"#);
    asse_ne("", r#"{ 'a' } = { 'b' }"#);
    asse_ne("", r#"{ '\0' } = { '\u{0}' }"#);
}

#[test]
fn test_unevaled_str_lits() {
    asse_eq("", r#"{ "hello" } = { "hello" }"#);
    asse_eq("", r#"{ "\0" } = { "\0" }"#);

    asse_ne("", r#"{ "hello" } = { "world" }"#);
    asse_ne("", r#"{ "hello" } = { r"hello" }"#);
    asse_ne("", r##"{ "hello" } = { r#"hello"# }"##);

    asse_ne("", r#"{ "\0" } = { "\u{0}" }"#);
}

#[test]
fn test_unevaled_idents() {
    asse_eq("", "{ foo bar } = { foo bar }");
    asse_eq("", "{ r#foo bar } = { foo r#bar }");

    asse_ne("", "{ foo bar } = { a b }");
}

#[test]
fn test_unevaled_eq_delims() {
    asse_eq("", "{ { a } } = { { a } }");
    asse_eq("", "{ { a } } = { { r#a } }");

    asse_eq("", "{ [ a ] } = { [ a ] }");
    asse_eq("", "{ [ a ] } = { [ r#a ] }");

    asse_eq("", "{ ( a ) } = { ( a ) }");
    asse_eq("", "{ ( a ) } = { ( r#a ) }");
}

#[test]
fn test_unevaled_ne_delims() {
    asse_ne("", "{ { a } } = { { b } }");
    asse_ne("", "{ { a } } = { [ a ] }");
    asse_ne("", "{ { a } } = { ( a ) }");

    asse_ne("", "{ [ a ] } = { [ b ] }");
    asse_ne("", "{ [ a ] } = { { a } }");
    asse_ne("", "{ [ a ] } = { ( a ) }");

    asse_ne("", "{ ( a ) } = { ( b ) }");
    asse_ne("", "{ ( a ) } = { { a } }");
    asse_ne("", "{ ( a ) } = { [ a ] }");
}


#[test]
fn test_unevaled_punct() {
    asse_eq("", "{ == } = { == }");

    asse_eq("", "{ << } = { << }");
    asse_eq("", "{ << } = { < < }");
    asse_eq("", "{ < < } = { << }");

    asse_eq("", "{ >> } = { >> }");
    asse_eq("", "{ >> } = { > > }");
    asse_eq("", "{ > > } = { >> }");
    
    asse_eq("", "{ Foo<<u32>::Bar<u32>> } = { Foo< <u32>::Bar<u32> > }");


    asse_ne("", "{ == } = { <= }");
    asse_ne("", "{ == } = { >= }");
    asse_ne("", "{ == } = { != }");
    asse_ne("", "{ < } = { > }");
    asse_ne("", "{ << } = { >> }");
}




























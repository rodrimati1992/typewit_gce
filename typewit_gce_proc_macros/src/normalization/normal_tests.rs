use crate::{
    error::Error,
    utils::CrateToken,
    SimplifyFraction,
};

use super::Polynomial;

#[track_caller]
pub(super) fn parse(
    s: &str, 
    simplify_rhs: SimplifyFraction,
) -> Result<(Polynomial, Polynomial), Error> {
    let input_tokens: crate::used_proc_macro::TokenStream = s.parse().unwrap();
    let iter = &mut input_tokens.into_iter().peekable();

    let crate_token = CrateToken {
        krate: "crate".parse().unwrap()
    };

    crate::__parse_polynomials(&crate_token, simplify_rhs, iter).map_err(|(_, e)| e)
}

#[track_caller]
fn asse_eq(s: &str) {
    let (l, r) = parse(s, SimplifyFraction::Yes).unwrap();

    assert_eq!(l, r, "{s}");
}

#[track_caller]
fn asse_ne(s: &str) {
    let (l, r) = parse(s, SimplifyFraction::Yes).unwrap();

    assert_ne!(l, r, "{s}");
}


#[test]
fn test_simples() {
    asse_eq("x = x");
    asse_ne("x = y");

    asse_eq("1 = 1");
    asse_eq("0 = 0");
    asse_eq("-1 = -1");
    asse_ne("1 = 2");
    asse_ne("0 = 1");
    asse_ne("-1 = 1");
    
    asse_eq("f() = f()");
    asse_ne("f() = g()");
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
    
    asse_ne("(f(y) + 0) * f(y) = f(y) * 1");
}

#[test]
fn test_distributive_single() {
    asse_eq("(x + 1) * 1 = x + 1");
    asse_eq("(x + 1) * -1 = -x - 1");
    asse_eq("(x + 1) * 2 = 2 * x + 2");
    asse_eq("(x + 1) * -2 = -2 * x - 2");
    asse_eq("-(x + 1) * -2 = 2 * x + 2");
    asse_eq("(x + 1) * x = x * x + x");
    
    asse_ne("(x + 1) * x = x * x + 1");
}

#[test]
fn test_distributive_double() {
    asse_eq("(x + 1) * (x + 1) = x * x + 2 * x + 1");
    
    asse_eq("(x - 1) * (x - 1) = x * x - 2 * x + 1");
    
    asse_ne("(x - 1) * (x - 1) = x * x + 2 * x + 1");
}

#[test]
fn test_distributive_double_multivariate() {
    asse_eq("(x + y) * (x + 1) = x * x + x + y * x + y");

    asse_eq("(x + y) * (3 * z + w) = 3 * x * z + x * w + 3 * y * z + y * w");
    asse_eq("(x + y) * (3 * z + w) = 3 * z * (x + y) + w * (x + y)");

    asse_ne("(x + y) * (3 * z + w) = 3 * z * (x + y) + w * (x + 1)");

}

#[test]
fn test_distributive_triple() {
    asse_eq("(x + 1) * (x + 1) * (x + 1) = x * x * x + 3 * x * x + 3 * x + 1");
    
    asse_eq("(x - 1) * (x - 1) * (x - 1) = x * x * x - 3 * x * x + 3 * x - 1");
    
    asse_ne("(x - 1) * (x - 1) * (x - 1) = x * x * x + 3 * x * x + 3 * x + 1");
}


#[test]
fn test_unevaled_lits() {
    asse_eq("{ 0i8 } = { 0u8 }");
    asse_eq("{ 0_i8 } = { 0_u8 }");
    asse_eq("{ -1_i8 } = { -1_isize }");

    asse_eq("{ 10.wrapping_add(0b111) } = { 0xA.wrapping_add(7) }");
    asse_eq("{ 0o12.wrapping_add(0b111) } = { 10.wrapping_add(7) }");
    
    asse_ne("{ 10 } = { 11 }");
    asse_ne("{ \"foo\" } = { b\"foo\" }");
}

#[test]
fn test_unevaled_char_lits() {
    asse_eq(r#"{ 'a' } = { 'a' }"#);
    asse_eq(r#"{ '\0' } = { '\0' }"#);

    asse_ne(r#"{ 'a' } = { b'a' }"#);
    asse_ne(r#"{ 'a' } = { 'b' }"#);
    asse_ne(r#"{ '\0' } = { '\u{0}' }"#);
}

#[test]
fn test_unevaled_str_lits() {
    asse_eq(r#"{ "hello" } = { "hello" }"#);
    asse_eq(r#"{ "\0" } = { "\0" }"#);

    asse_ne(r#"{ "hello" } = { "world" }"#);
    asse_ne(r#"{ "hello" } = { r"hello" }"#);
    asse_ne(r##"{ "hello" } = { r#"hello"# }"##);

    asse_ne(r#"{ "\0" } = { "\u{0}" }"#);
}

#[test]
fn test_unevaled_idents() {
    asse_eq("{ foo bar } = { foo bar }");
    asse_eq("{ r#foo bar } = { foo r#bar }");

    asse_ne("{ foo bar } = { a b }");
}

#[test]
fn test_unevaled_eq_delims() {
    asse_eq("{ { a } } = { { a } }");
    asse_eq("{ { a } } = { { r#a } }");

    asse_eq("{ [ a ] } = { [ a ] }");
    asse_eq("{ [ a ] } = { [ r#a ] }");

    asse_eq("{ ( a ) } = { ( a ) }");
    asse_eq("{ ( a ) } = { ( r#a ) }");
}

#[test]
fn test_unevaled_ne_delims() {
    asse_ne("{ { a } } = { { b } }");
    asse_ne("{ { a } } = { [ a ] }");
    asse_ne("{ { a } } = { ( a ) }");

    asse_ne("{ [ a ] } = { [ b ] }");
    asse_ne("{ [ a ] } = { { a } }");
    asse_ne("{ [ a ] } = { ( a ) }");

    asse_ne("{ ( a ) } = { ( b ) }");
    asse_ne("{ ( a ) } = { { a } }");
    asse_ne("{ ( a ) } = { [ a ] }");
}


#[test]
fn test_unevaled_punct() {
    asse_eq("{ == } = { == }");

    asse_eq("{ << } = { << }");
    asse_eq("{ << } = { < < }");
    asse_eq("{ < < } = { << }");

    asse_eq("{ >> } = { >> }");
    asse_eq("{ >> } = { > > }");
    asse_eq("{ > > } = { >> }");
    
    asse_eq("{ Foo<<u32>::Bar<u32>> } = { Foo< <u32>::Bar<u32> > }");


    asse_ne("{ == } = { <= }");
    asse_ne("{ == } = { >= }");
    asse_ne("{ == } = { != }");
    asse_ne("{ < } = { > }");
    asse_ne("{ << } = { >> }");
}




























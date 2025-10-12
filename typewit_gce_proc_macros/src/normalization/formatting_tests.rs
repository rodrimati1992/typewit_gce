use crate::{
    utils::CrateToken,
    SimplifyFraction,
};

#[track_caller]
fn roundtrip(s: &str) -> String {
    let input_tokens: crate::used_proc_macro::TokenStream = s.parse().unwrap();
    let iter = &mut input_tokens.into_iter().peekable();

    let crate_token = CrateToken {
        krate: "crate".parse().unwrap()
    };

    let poly = crate::__parse_one_polynomial(&crate_token, SimplifyFraction::Yes, iter)
        .map_err(|(_, e)| e)
        .unwrap();

    format!("{poly}")
}

#[track_caller]
fn assert_roundtrip(s: &str) {
    assert_eq!(roundtrip(s), s);
}

#[test]
fn mul_fmt_test() {
    assert_roundtrip("3");
    assert_roundtrip("- 3");

    assert_eq!(roundtrip("X * (3 + Y)"), "3 * X + X * Y");
    assert_eq!(roundtrip("X * (3 - Y)"), "3 * X - X * Y");
}

#[test]
fn pow_fmt_test() {
    assert_eq!(roundtrip("X * X"), "X**2");
    assert_eq!(roundtrip("aaa(5) * aaa(5) * aaa(5)"), "aaa(5)**3");
    assert_eq!(roundtrip("aaa(5) * -aaa(5) * aaa(5)"), "- aaa(5)**3");
    assert_eq!(roundtrip("aaa(5) * aaa(5) * 10 * aaa(5)"), "10 * aaa(5)**3");
}

#[test]
fn div_fmt_test() {
    assert_roundtrip("1 / X");
    assert_eq!(roundtrip("1 % X % Y / Z"), "((1 % X) % Y) / Z");
    assert_eq!(roundtrip("1 / X / Y / Z"), "((1 / X) / Y) / Z");
    assert_eq!(roundtrip("1 / X * Y / Z / W"), "((Y * 1 / X) / Z) / W");
    assert_roundtrip("aaa(3) / self::bbb(5)");
    assert_roundtrip("aaa(3) / (2 + self::bbb(5))");
}

#[test]
fn div_pow_fmt_test() {
    assert_eq!(roundtrip("(1/X) * (1/X)"), "(1 / X)**2");
    assert_eq!(roundtrip("(1/X) * (-1/X)"), "- (1 / X)**2");
    assert_eq!(roundtrip("(1/X) * (1/-X)"), "- (1 / X)**2");
    assert_eq!(roundtrip("(1/X) * -(1/X)"), "- (1 / X)**2");
    assert_eq!(roundtrip("-(1/X) * -(1/X)"), "(1 / X)**2");
    assert_eq!(roundtrip("(1/X) * (1/X) * (1/X)"), "(1 / X)**3");
}


#[test]
fn rem_fmt_test() {
    assert_roundtrip("1 % X");

    assert_roundtrip("aaa(3) % self::bbb(5)");
    assert_roundtrip("aaa(3) % (2 + self::bbb(5))");
}

#[test]
fn rem_pow_fmt_test() {
    assert_eq!(roundtrip("(1 % X) * (1 % X)"), "(1 % X)**2");
}





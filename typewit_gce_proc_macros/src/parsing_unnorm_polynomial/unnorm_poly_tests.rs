use crate::error::Error;

use super::{UnnormMulExpr as UME, UnnormFunctionCall};


fn flatten_poly(poly: super::UnnormPolynomial) -> Vec<Vec<UME>> {
    poly.terms.into_iter().map(|term| term.mul_exprs).collect()
}

fn parse(s: &str) -> Result<Vec<Vec<UME>>, Error> {
    let ts: crate::used_proc_macro::TokenStream = s.parse().unwrap();
    super::parse_polynomial(&mut ts.into_iter().peekable()).map(flatten_poly)
}

fn constant(n: i128) -> UME {
    UME::Constant(n.into())
}
fn variable(s: &str) -> UME {
    UME::Variable(s.into())
}


#[test]
fn numeric_literals() {
    assert_eq!(parse("0x10u32").unwrap(), vec![vec![constant(16)]]);
    assert_eq!(parse("0x10_u32").unwrap(), vec![vec![constant(16)]]);
    assert_eq!(parse("0x1_0_u32").unwrap(), vec![vec![constant(16)]]);
    assert_eq!(parse("0x_1_0_u32").unwrap(), vec![vec![constant(16)]]);
    
    assert_eq!(parse("0b10i32").unwrap(), vec![vec![constant(2)]]);
    assert_eq!(parse("0b11_i32").unwrap(), vec![vec![constant(3)]]);
    
    assert_eq!(parse("-53_i32").unwrap(), vec![vec![constant(-1), constant(53)]]);
    assert_eq!(parse("-76i32").unwrap(), vec![vec![constant(-1), constant(76)]]);
}

#[test]
fn basic_arith_ops() {
    for s in [
        " 1+1-2+1*B/C%D*20",
        "+1+1-2+1*B/C%D*20",
        "+&1+1-&2+1*&B/&C%&D*&20",
    ] {
        assert_eq!(
            parse(s).unwrap(),
            vec![
                vec![constant(1)],
                vec![constant(1)],
                vec![constant(-1), constant(2)],
                vec![
                    UME::FunctionCall(UnnormFunctionCall::Rem(
                        vec![
                            UME::FunctionCall(UnnormFunctionCall::Div(
                                vec![constant(1), variable("B")].into(),
                                vec![variable("C")].into(),
                            ))
                        ].into(),
                        vec![variable("D")].into(),
                    )),
                    constant(20),
                ],
            ]
        );
    }
}

#[test]
fn minus_prefix() {
    assert_eq!(
        parse("-1*2+2").unwrap(),
        vec![vec![constant(-1), constant(1), constant(2)],vec![constant(2)]]
    );

    assert_eq!(
        parse("--1*2+2").unwrap(),
        vec![vec![constant(1), constant(2)],vec![constant(2)]]
    );

    assert_eq!(
        parse("---1*2+2").unwrap(),
        vec![vec![constant(-1), constant(1), constant(2)],vec![constant(2)]]
    );

    assert_eq!(
        parse("----1*2+2").unwrap(),
        vec![vec![constant(1), constant(2)],vec![constant(2)]]
    );
}


#[test]
fn unary_minus() {
    for odd_minus in [
        "2*-3",
        "2*---3",
        "2*-----3",
    ] {
        println!("{odd_minus:?}");
        assert_eq!(parse(odd_minus).unwrap(), vec![vec![constant(2), constant(-1), constant(3)]]);
    }

    for even_minus in [
        "2*--3",
        "2*----3",
        "2*------3",
    ] {
        println!("{even_minus:?}");
        assert_eq!(parse(even_minus).unwrap(), vec![vec![constant(2), constant(3)]]);
    }
}

#[test]
fn function_call() {
    assert_eq!(
        parse("foo()").unwrap(),
        vec![vec![
            UME::FunctionCall(UnnormFunctionCall::Other {
                name: "foo".into(),
                args: vec![],
            }),
        ]]
    );

    assert_eq!(
        parse("1*-foo()").unwrap(),
        vec![vec![
            constant(1),
            constant(-1),
            UME::FunctionCall(UnnormFunctionCall::Other {
                name: "foo".into(),
                args: vec![],
            }),
        ]]
    );

    assert_eq!(
        parse("-foo()").unwrap(),
        vec![vec![
            constant(-1),
            UME::FunctionCall(UnnormFunctionCall::Other {
                name: "foo".into(),
                args: vec![],
            }),
        ]]
    );

    assert_eq!(
        parse("foo(1)").unwrap(),
        vec![vec![
            UME::FunctionCall(UnnormFunctionCall::Other {
                name: "foo".into(),
                args: vec![vec![vec![constant(1)]].into()],
            }),
        ]]
    );

    assert_eq!(
        parse("bar(2 * X + 3, 4)").unwrap(),
        vec![vec![
            UME::FunctionCall(UnnormFunctionCall::Other {
                name: "bar".into(),
                args: vec![
                    vec![vec![constant(2), variable("X")], vec![constant(3)]].into(), 
                    vec![vec![constant(4)]].into(),
                ],
            }),
        ]]
    );

    assert_eq!(
        parse("baz(1,2,)").unwrap(),
        vec![vec![
            UME::FunctionCall(UnnormFunctionCall::Other {
                name: "baz".into(),
                args: vec![
                    vec![vec![constant(1)]].into(), 
                    vec![vec![constant(2)]].into(),
                ],
            }),
        ]]
    );
}



#[test]
fn invalid_inputs() {
    _ = parse("").unwrap_err();
    _ = parse("\"fooo\"").unwrap_err();
    _ = parse("10+").unwrap_err();
    _ = parse("10+").unwrap_err();
    _ = parse("10*-").unwrap_err();
    _ = parse("10*+").unwrap_err();
    _ = parse("10*").unwrap_err();
    _ = parse("10/").unwrap_err();
    _ = parse("10%").unwrap_err();
}
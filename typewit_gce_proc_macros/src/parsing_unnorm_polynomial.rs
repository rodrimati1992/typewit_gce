#![deny(unused_results)]

use crate::error::Error;

use crate::used_proc_macro::{self, Delimiter, Punct, Spacing, Span, TokenTree as TT};

use crate::utils::bi_eq;

use num_bigint::BigInt;
use num_traits::Num;


#[cfg(test)]
mod unnorm_poly_tests;


#[derive(Debug, PartialEq)]
pub(crate) struct UnnormPolynomial {
    pub(crate) terms: Vec<UnnormPolynomialTerm>,
}

#[derive(Debug, PartialEq)]
pub(crate) struct UnnormPolynomialTerm {
    pub(crate) mul_exprs: Vec<UnnormMulExpr>,
}

#[derive(Debug, PartialEq)]
pub(crate) enum UnnormMulExpr {
    Constant(BigInt),
    Variable(String),
    FunctionCall(UnnormFunctionCall),
    Parenthesis(UnnormPolynomial),
}

#[derive(Debug, PartialEq)]
pub(crate) enum UnnormFunctionCall {
    Rem(Vec<UnnormMulExpr>, Box<UnnormMulExpr>),
    Div(Vec<UnnormMulExpr>, Box<UnnormMulExpr>),
    Other {
        name: String,
        args: Vec<UnnormPolynomial>
    },
}

impl From<Vec<Vec<UnnormMulExpr>>> for UnnormPolynomial {
    fn from(vv: Vec<Vec<UnnormMulExpr>>) -> Self {
        Self {
            terms: vv.into_iter()
                .map(|mul_exprs| UnnormPolynomialTerm { mul_exprs })
                .collect()
        }
    }
}

pub(crate) type Parser = std::iter::Peekable<used_proc_macro::token_stream::IntoIter>;

pub(crate) fn parse_polynomial(parser: &mut Parser) -> Result<UnnormPolynomial, Error> {
    // needed to shrink the lifetime argument of `&mut Parser`
    let mut parser = parser;
    let mut inner_parser;

    let mut out = UnnormPolynomial {
        terms: Vec::new(),
    };

    if let Some(TT::Group(group)) = parser.peek() && group.delimiter() == Delimiter::None {
        inner_parser = group.stream().into_iter().peekable();
        _ = parser.next();
        parser = &mut inner_parser;
    }

    if parser.peek().is_none() {
        return Err(Error::new(Span::call_site(), "expected polynomial, passed nothing"));
    }

    loop {
        let poked = parser.peek();

        let mut term = UnnormPolynomialTerm {
            mul_exprs: Vec::new(),
        };

        match poked {
            Some(tt) if end_of_expr(tt) => {
                break
            }
            None => {
                break
            }
            Some(TT::Punct(p)) if p.as_char() == '-' => {
                if let Some(neg) = parse_neg(parser) {
                    term.mul_exprs.push(neg);
                }
            }
            Some(TT::Punct(p)) if p.as_char() == '+' => {
                _ = parser.next();
            }
            _ => {}
        }
        
        parse_term_inner(&mut term, parser)?;

        out.terms.push(term);
    }

    Ok(out)
}

fn parse_term_inner(
    term: &mut UnnormPolynomialTerm, 
    parser: &mut Parser,
) -> Result<(), Error> {
    let mut has_parsed_one = false;
    loop {
        match parser.peek() {
            Some(TT::Group(_) | TT::Ident(_) | TT::Literal(_)) => {
                parse_mul_subexpr(&mut term.mul_exprs, parser)?;
            }
            Some(TT::Punct(p)) if p.as_char() == '*' => {
                _ = parser.next();
                parse_mul_subexpr(&mut term.mul_exprs, parser)?;
            }
            Some(TT::Punct(p)) if p.as_char() == '%' => {
                _ = parser.next();
                let mut rhs = Vec::new();
                parse_mul_subexpr(&mut rhs, parser)?;
                let [rhs] = <[_; 1]>::try_from(rhs).unwrap();

                let remm = if let UnnormMulExpr::Constant(lit) = &rhs && bi_eq(lit, 1) {
                    // `X % 1 == X * 0` 
                    UnnormMulExpr::Constant(BigInt::ZERO)
                } else {                
                    let lhs = term.mul_exprs.drain(..).collect();
                    UnnormMulExpr::FunctionCall(UnnormFunctionCall::Rem(lhs, rhs.into()))
                };

                term.mul_exprs.push(remm);
            }
            Some(TT::Punct(p)) if p.as_char() == '/' => {
                _ = parser.next();
                let mut rhs = Vec::new();
                parse_mul_subexpr(&mut rhs, parser)?;
                let [rhs] = <[_; 1]>::try_from(rhs).unwrap();

                // `X / 1 == X` so nothing is added in that case
                if !matches!(&rhs, UnnormMulExpr::Constant(lit) if !bi_eq(lit, 1)) {
                    let lhs = term.mul_exprs.drain(..).collect();
                    term.mul_exprs.push(
                        UnnormMulExpr::FunctionCall(UnnormFunctionCall::Div(lhs, rhs.into()))
                    );
                }
            }
            Some(tt) =>  {
                if has_parsed_one {
                    return Ok(())
                } else {
                    return Err(Error::new(tt.span(), "empty polynomial term"))
                }
            }
            None if !has_parsed_one => {
                return Err(Error::new(Span::call_site(), "empty polynomial term"))
            }
            None => {
                return Ok(())
            }
        }

        has_parsed_one = true;
    }
}

/// returns an error if there's no expression
fn parse_mul_subexpr(mul_exprs: &mut Vec<UnnormMulExpr>, parser: &mut Parser) -> Result<(), Error> {
    match parser.peek() {
        Some(TT::Group(group)) if group.delimiter() == Delimiter::Parenthesis => {
            let iter = &mut group.stream().into_iter().peekable();
            _ = parser.next();

            mul_exprs.push(UnnormMulExpr::Parenthesis(parse_polynomial(iter)?));
        }
        Some(tt) if start_of_path(tt) => {
            let path = parse_path(parser)?;

            mul_exprs.push(parse_var_or_func(path, parser)?)
        }
        Some(TT::Literal(lit)) => {
            mul_exprs.push(parse_int(lit.span(), &lit.to_string())?);
            _ = parser.next();
        }
        Some(TT::Punct(p)) if p.as_char() == '-' => {
            if let Some(neg) = parse_neg(parser) {
                mul_exprs.push(neg);
            }
            parse_mul_subexpr(mul_exprs, parser)?;
        }
        Some(tt) => return Err(Error::new(tt.span(), "expected expression")),
        None => return Err(Error::new(Span::call_site(), "expected expression")),
    }

    Ok(())
}


fn parse_neg(parser: &mut Parser) -> Option<UnnormMulExpr> {
    _ = parser.next();
    let mut neg = -1;
    while let Some(TT::Punct(p)) = parser.peek() && p.as_char() == '-' {
        neg = -neg;
        _ = parser.next();
    }

    (neg == -1).then(|| UnnormMulExpr::Constant(BigInt::from(neg)))    
}


fn parse_var_or_func(
    name: String,
    parser: &mut Parser,
) -> Result<UnnormMulExpr, Error> {
    match parser.peek() {
        Some(TT::Group(group)) if group.delimiter() == Delimiter::Parenthesis => {
            let iter = &mut group.stream().into_iter().peekable();

            let mut args = Vec::new();

            while iter.peek().is_some() {
                args.push(parse_polynomial(iter)?);

                match iter.peek() {
                    None => break,
                    Some(TT::Punct(p)) if p.as_char() == ',' => {}
                    Some(tt) => return Err(Error::new(tt.span(), "expected comma"))
                }
                _ = iter.next();
            }

            // consume the parenthesis
            _ = parser.next();

            Ok(UnnormMulExpr::FunctionCall(UnnormFunctionCall::Other { name, args }))
        }
        _ => {
            Ok(UnnormMulExpr::Variable(name))
        }
    }
}

/// Panics if the first token isn't an Ident
fn start_of_path(tt: &TT) -> bool {
    matches!(tt, TT::Ident(_)) || 
    matches!(tt, TT::Punct(p) if is_double_colon(p))
}

/// Panics if the first token isn't an Ident
fn parse_path(parser: &mut Parser) -> Result<String, Error> {
    let mut out = String::new();
    
    loop {
        match parser.peek() {
            Some(TT::Punct(p)) if is_double_colon(&p) => {
                _ = parser.next();
                
                match parser.next().expect("no join token before nothing") {
                    TT::Punct(p) if is_single_colon(&p) => {
                        out.push_str("::")
                    }
                    token => return Err(Error::new(token.span(), "expected `:`"))
                }
            }
            Some(TT::Ident(ident))  => {
                out.push_str(ident.to_string().trim_start_matches("r#"));
                
                _ = parser.next();
            }
            _ => return Ok(out),
        }
    }
}

fn parse_int(span: Span, str: &str) -> Result<UnnormMulExpr, Error> {
    let str = str.trim().replace("_", "");

    let (base, digits) = if let Some(stripped) = str.strip_prefix("0b") {
        (2, stripped)
    } else if let Some(stripped) = str.strip_prefix("0o") {
        (8, stripped)
    } else if let Some(stripped) = str.strip_prefix("0x") {
        (16, stripped)
    } else {
        (10, &*str)
    };

    BigInt::from_str_radix(digits, base)
        .map(UnnormMulExpr::Constant)
        .map_err(|_| Error::new(span, "could not parse as integer"))
}

fn end_of_expr(tt: &TT) -> bool {
    match tt {
        TT::Punct(p) => {
            p.as_char() == ':' && p.spacing() == Spacing::Alone
            || p.as_char() == ','
            || p.as_char() == '='
        }
        _ => false,
    }
}

fn is_single_colon(p: &Punct) -> bool {
    p.as_char() == ':' && p.spacing() == Spacing::Alone
}

fn is_double_colon(p: &Punct) -> bool {
    p.as_char() == ':' && p.spacing() == Spacing::Joint
}




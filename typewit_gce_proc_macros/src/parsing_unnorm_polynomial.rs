#![deny(unused_results)]

use crate::error::Error;

use crate::used_proc_macro::{self, Delimiter, Group, Punct, Spacing, Span, TokenTree as TT};

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
    Rem(UnnormPolynomialTerm, UnnormPolynomialTerm),
    Div(UnnormPolynomialTerm, UnnormPolynomialTerm),
    Other {
        name: String,
        args: Vec<UnnormPolynomial>
    },
}

impl From<Vec<Vec<UnnormMulExpr>>> for UnnormPolynomial {
    fn from(vv: Vec<Vec<UnnormMulExpr>>) -> Self {
        Self {
            terms: vv.into_iter()
                .map(UnnormPolynomialTerm::from)
                .collect()
        }
    }
}

impl From<Vec<UnnormMulExpr>> for UnnormPolynomialTerm {
    fn from(mul_exprs: Vec<UnnormMulExpr>) -> Self {
        Self { mul_exprs }
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

    if let Some(group) = opt_parse_group(parser, |g| g.delimiter() == Delimiter::None) {
        inner_parser = group.stream().into_iter().peekable();
        _ = parser.next();
        parser = &mut inner_parser;
    }

    if parser.peek().is_none() {
        return Err(Error::new(Span::call_site(), "expected polynomial, passed nothing"));
    }

    loop {
        let mut term = UnnormPolynomialTerm {
            mul_exprs: Vec::new(),
        };

        match parser.peek() {
            Some(tt) if end_of_expr(tt) => {
                break
            }
            None => {
                break
            }
            Some(TT::Punct(p)) if p.as_char() == '+' => {
                _ = parser.next();
            }
            _ => {}
        }
        if let Some(TT::Punct(p)) = parser.peek() 
        && p.as_char() == '-'
        && let Some(Signedness::Negative(neg)) = opt_parse_neg(parser)
        {
            term.mul_exprs.push(neg);
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
        if let Some(TT::Group(_) | TT::Ident(_) | TT::Literal(_)) = parser.peek() {
            parse_mul_subexpr(&mut term.mul_exprs, parser)?;
        } else if let Some(path) = opt_parse_path(parser)? { 
            term.mul_exprs.push(parse_var_or_func(path, parser)?)
        } else if opt_parse_punct(parser, |p| p.as_char() == '*') {
            parse_mul_subexpr(&mut term.mul_exprs, parser)?;
        } else if opt_parse_punct(parser, |p| p.as_char() == '%') {
            let mut rhs = Vec::new();
            parse_mul_subexpr(&mut rhs, parser)?;

            let remm = if let [UnnormMulExpr::Constant(lit)] = &rhs[..] && bi_eq(lit, 1) {
                // `X % 1 == X * 0` 
                UnnormMulExpr::Constant(BigInt::ZERO)
            } else {                
                let lhs = UnnormPolynomialTerm { 
                    mul_exprs: term.mul_exprs.drain(..).collect(),
                };
                let rhs = UnnormPolynomialTerm { mul_exprs: rhs };
                UnnormMulExpr::FunctionCall(UnnormFunctionCall::Rem(lhs, rhs))
            };

            term.mul_exprs.push(remm);
        } else if opt_parse_punct(parser, |p| p.as_char() == '/') {
            let mut rhs = Vec::new();
            parse_mul_subexpr(&mut rhs, parser)?;

            // `X / 1 == X` so nothing is added in that case
            if !matches!(&rhs[..], [UnnormMulExpr::Constant(lit)] if bi_eq(lit, 1)) {
                let lhs = UnnormPolynomialTerm { 
                    mul_exprs: term.mul_exprs.drain(..).collect(),
                };
                let rhs = UnnormPolynomialTerm { mul_exprs: rhs };
                term.mul_exprs.push(
                    UnnormMulExpr::FunctionCall(UnnormFunctionCall::Div(lhs, rhs))
                );
            }
        } else if opt_parse_punct(parser, |p| p.as_char() == '&') {
            // ignore borrows
            continue;
        } else if let Some(tt) = parser.peek() {
            if has_parsed_one {
                return Ok(())
            } else {
                return Err(Error::new(tt.span(), "empty polynomial term"))
            }
        } else if has_parsed_one {
            return Ok(())
        } else {
            return Err(Error::new(Span::call_site(), "empty polynomial term"))
        }

        has_parsed_one = true;
    }
}



/// returns an error if there's no expression
fn parse_mul_subexpr(mul_exprs: &mut Vec<UnnormMulExpr>, parser: &mut Parser) -> Result<(), Error> {
    if let Some(group) = opt_parse_group(parser, |g| g.delimiter() == Delimiter::Parenthesis) {
        let iter = &mut group.stream().into_iter().peekable();

        mul_exprs.push(UnnormMulExpr::Parenthesis(parse_polynomial(iter)?));
    } else if let Some(path) = opt_parse_path(parser)? {
        mul_exprs.push(parse_var_or_func(path, parser)?)
    } else if let Some(TT::Literal(lit)) = parser.peek() {
        mul_exprs.push(parse_int(lit.span(), &lit.to_string())?);
        _ = parser.next();
    } else if opt_parse_punct(parser, |p| p.as_char() == '&') {
        // ignore borrows
        parse_mul_subexpr(mul_exprs, parser)?;
    } else if let Some(signedness) = opt_parse_neg(parser) {
        if let Signedness::Negative(neg) = signedness {
            mul_exprs.push(neg);
        }
        parse_mul_subexpr(mul_exprs, parser)?;
    } else if let Some(tt) = parser.peek() {
        return Err(Error::new(tt.span(), "expected expression"))
    } else {
        return Err(Error::new(Span::call_site(), "expected expression"))
    }

    Ok(())
}


enum Signedness {
    Positive,
    Negative(UnnormMulExpr),
}

fn opt_parse_neg(parser: &mut Parser) -> Option<Signedness> {
    if opt_parse_punct(parser, |p| p.as_char() == '-') {
        let mut neg = -1;
        while opt_parse_punct(parser, |p| p.as_char() == '-') {
            neg = -neg;
        }

        Some(if neg == -1 {
            Signedness::Negative(UnnormMulExpr::Constant(BigInt::from(neg)))
        } else {
            Signedness::Positive
        })
    } else {
        None
    }
}


fn parse_var_or_func(
    name: String,
    parser: &mut Parser,
) -> Result<UnnormMulExpr, Error> {
    if let Some(group) = opt_parse_group(parser, |g| g.delimiter() == Delimiter::Parenthesis) {
        let iter = &mut group.stream().into_iter().peekable();

        let mut args = Vec::new();

        while iter.peek().is_some() {
            args.push(parse_polynomial(iter)?);

            match iter.peek() {
                None => break,
                Some(TT::Punct(p)) if p.as_char() == ',' => _ = iter.next(),
                Some(tt) => return Err(Error::new(tt.span(), "expected comma"))
            }
        }

        Ok(UnnormMulExpr::FunctionCall(UnnormFunctionCall::Other { name, args }))
    } else {
        Ok(UnnormMulExpr::Variable(name))
    }
}

fn opt_parse_punct(parser: &mut Parser, pred: impl Fn(&Punct) -> bool) -> bool {
    if let Some(TT::Punct(p)) = parser.peek() && pred(p) {
        _ = parser.next();
        true
    } else {
        false
    }
}

fn opt_parse_group(
    parser: &mut Parser,
    pred: impl Fn(&Group) -> bool,
) -> Option<Group> {
    if let Some(TT::Group(p)) = parser.peek()
    && pred(p)
    {
        let Some(TT::Group(g)) = parser.next() else { unreachable!() };
        Some(g)
    } else {
        None
    }
}

fn opt_parse_path(parser: &mut Parser) -> Result<Option<String>, Error> {
    if parser.peek().is_some_and(start_of_path) { 
        parse_path(parser).map(Some)
    } else {
        Ok(None)
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




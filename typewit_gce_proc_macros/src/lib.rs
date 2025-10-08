use proc_macro2 as used_proc_macro;

use used_proc_macro::{Delimiter, Span, TokenStream, TokenTree as TT};

use crate::{
    normalization::Polynomial,
    utils::CrateToken,
};


mod error;
mod parsing_unnorm_polynomial;
mod utils;
mod normalization;


fn parse_crate_token(tt: Option<TT>) -> CrateToken {
    match tt {
        Some(TT::Group(group)) if group.delimiter() == Delimiter::Parenthesis => {
            CrateToken {
                krate: group.stream()
            }
        }
        _ => {
            panic!("proc macros aren't invoked directly, so $crate is always passed")
        }
    }
}


fn __parse_polynomials(
    crate_path: &CrateToken,
    iter: &mut std::iter::Peekable<used_proc_macro::token_stream::IntoIter>,
) -> Result<(Polynomial, Polynomial), (CrateToken, crate::error::Error)> {

    let lhs_poly = parsing_unnorm_polynomial::parse_polynomial(iter)
        .map_err(|e| (crate_path.clone(), e))
        .map(normalization::normalize_polynomial)?;

    if let Some(TT::Punct(p)) = iter.peek()
    && let ',' | '=' = p.as_char()
    {
        _ = iter.next();
    }

    let rhs_poly = parsing_unnorm_polynomial::parse_polynomial(iter)
        .map_err(|e| (crate_path.clone(), e))
        .map(normalization::normalize_polynomial)?;

    Ok((lhs_poly, rhs_poly))
}

fn __assert_equal(input_tokens: TokenStream) -> Result<(), (CrateToken, crate::error::Error)> {
    let iter = &mut input_tokens.into_iter().peekable();

    let crate_path = parse_crate_token(iter.next());

    let (lhs_poly, rhs_poly) = __parse_polynomials(&crate_path, iter)?;

    if lhs_poly == rhs_poly {
        Ok(())
    } else {
        Err((
            crate_path,
            crate::error::Error::new(Span::call_site(), "cannot prove expressions are equal"),
        ))
    }
}

#[doc(hidden)]
#[proc_macro]
pub fn assert_equal(input_tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match __assert_equal(input_tokens.into()) {
        Ok(_) => proc_macro::TokenStream::new(),
        Err((crate_path, e)) => e.to_compile_error(crate_path).into(),
    }
}

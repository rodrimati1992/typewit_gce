use proc_macro2 as used_proc_macro;

use used_proc_macro::{Delimiter, Group, Span, TokenStream, TokenTree as TT};

use crate::{
    normalization::Polynomial,
    utils::CrateToken,
};


mod error;
mod parsing_unnorm_polynomial;
mod utils;
mod unevaled_expr;
mod normalization;

mod i129;
mod nonzeroi129;


#[derive(Copy, Clone)]
enum SimplifyFraction {
    Yes,
    #[cfg(test)]
    No,
}

impl SimplifyFraction {
    fn is_no(self) -> bool {
        !matches!(self, Self::Yes)
    }
    fn is_yes(self) -> bool {
        matches!(self, Self::Yes)
    }
}



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


fn __parse_one_polynomial(
    crate_path: &CrateToken,
    simplify_fraction: SimplifyFraction,
    iter: &mut std::iter::Peekable<used_proc_macro::token_stream::IntoIter>,
) -> Result<Polynomial, (CrateToken, crate::error::Error)> {
    let unnorm = parsing_unnorm_polynomial::parse_polynomial(iter)
        .map_err(|e| (crate_path.clone(), e))?;

    normalization::normalize_polynomial(unnorm, simplify_fraction)
        .map_err(|e| (
            crate_path.clone(), 
            crate::error::Error::new(Span::call_site(), e.to_string())
        ))
}

fn __parse_polynomials(
    crate_path: &CrateToken,
    simplify_rhs: SimplifyFraction,
    iter: &mut std::iter::Peekable<used_proc_macro::token_stream::IntoIter>,
) -> Result<(Polynomial, Polynomial), (CrateToken, crate::error::Error)> {
    let lhs_poly = __parse_one_polynomial(crate_path, SimplifyFraction::Yes, iter)?;

    if let Some(TT::Punct(p)) = iter.peek()
    && let ',' | '=' = p.as_char()
    {
        _ = iter.next();
    }

    let rhs_poly = __parse_one_polynomial(crate_path, simplify_rhs, iter)?;

    Ok((lhs_poly, rhs_poly))
}

fn __assert_equal(input_tokens: TokenStream) -> Result<(), (CrateToken, crate::error::Error)> {
    let iter = &mut input_tokens.into_iter().peekable();

    let crate_path = parse_crate_token(iter.next());

    let (lhs_poly, rhs_poly) = __parse_polynomials(&crate_path, SimplifyFraction::Yes, iter)?;

    if lhs_poly == rhs_poly {
        Ok(())
    } else {
        Err((
            crate_path,
            crate::error::Error::new(
                Span::call_site(), 
                format!("\
                    Cannot prove that the arguments are equal.\n\
                    This is their normalized representation:\n\
                     left: `{lhs_poly}`\n\
                    right: `{rhs_poly}`\n\
                ")
            ),
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

#[doc(hidden)]
#[proc_macro]
pub fn call_equality_proof_fn(input_tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    use std::iter::once;

    let span = Span::call_site();

    let mut iter = TokenStream::from(input_tokens).into_iter();
    
    let Some(recv @ TT::Ident(_)) = iter.next() else { unreachable!("internal macro") };
    let Some(TT::Group(group_lhs)) = iter.next() else { unreachable!("internal macro") };
    let Some(TT::Group(group_rhs)) = iter.next() else { unreachable!("internal macro") };

    let mut out = TokenStream::new();

    fn get_first_last_spans(ts: TokenStream) -> (Span, Span) {
        let mut iter = ts.into_iter().map(|tt| tt.span());

        match (iter.next(), iter.last()) {
            (Some(first), Some(last)) => (first, last),
            (Some(first), None) => (first, first),
            _ => (Span::call_site(), Span::call_site()),
        }
    }

    let lhs_def_span = group_lhs.span();
    let (lhs_start_span, lhs_end_span) = get_first_last_spans(group_lhs.stream());
    let rhs_def_span = group_rhs.span();
    let (rhs_start_span, rhs_end_span) = get_first_last_spans(group_rhs.stream());

    fn braced_expr(ts: TokenStream, start_span: Span, end_span: Span, def_span: Span) -> TT {
        let mut group = Group::new(Delimiter::Brace, ts);
        let span = start_span.join(end_span).unwrap_or(def_span);
        group.set_span(span);
        TT::Group(group)
    }

    out.extend(once(recv));
    out.extend(crate::utils::punct_token('.', span));
    out.extend(crate::utils::ident_token("get_equality_proof", span));
    out.extend(crate::utils::colon2_token(span));
    out.extend(crate::utils::punct_token('<', span));
    out.extend(once(braced_expr(group_lhs.stream(), lhs_start_span, lhs_end_span, lhs_def_span)));
    out.extend(crate::utils::punct_token(',', span));
    out.extend(once(braced_expr(group_rhs.stream(), rhs_start_span, rhs_end_span, rhs_def_span)));
    out.extend(crate::utils::punct_token('>', span));
    out.extend(once(crate::utils::paren(span, |_| {})));

    out.into()
}


use proc_macro2 as used_proc_macro;

use used_proc_macro::{Delimiter, TokenStream, TokenTree as TT};

use crate::utils::CrateToken;


mod error;
mod parsing_unnorm_polynomial;
mod utils;


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


fn __assert_equal(input_tokens: TokenStream) -> Result<(), (CrateToken, crate::error::Error)> {
    let iter = &mut input_tokens.into_iter().peekable();

    let crate_path = parse_crate_token(iter.next());

    let unnorm_lhs_poly = parsing_unnorm_polynomial::parse_polynomial(iter)
        .map_err(|e| (crate_path.clone(), e))?;

    let unnorm_rhs_poly = parsing_unnorm_polynomial::parse_polynomial(iter)
        .map_err(|e| (crate_path.clone(), e))?;

    Ok(())
}

#[doc(hidden)]
#[proc_macro]
pub fn assert_equal(input_tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match __assert_equal(input_tokens.into()) {
        Ok(_) => proc_macro::TokenStream::new(),
        Err((crate_path, e)) => e.to_compile_error(crate_path).into(),
    }
}

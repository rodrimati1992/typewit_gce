use std::iter::once;

use crate::used_proc_macro::{Literal, Span, TokenTree, TokenStream};

use crate::utils::CrateToken;


#[derive(Debug)]
pub(crate) struct Error {
    span: Span,
    error: &'static str,
}

impl Error {
    pub(crate) fn new(span: Span, error: &'static str) -> Self {
        Self {
            span,
            error,
        }
    }

    pub(crate) fn to_compile_error(&self, krate: CrateToken) -> TokenStream {
        let Error { error, span } = *self;

        let mut out = TokenStream::new();

        out.extend(krate.krate);
        out.extend(crate::utils::colon2_token(span));
        out.extend(crate::utils::ident_token("__", span));
        out.extend(crate::utils::colon2_token(span));

        out.extend(crate::utils::ident_token("compile_error", span));

        out.extend(crate::utils::punct_token('!', span));

        let msg_paren = crate::utils::paren(span, |ts| {
            let mut msg = Literal::string(error);
            msg.set_span(self.span);
            let msg = TokenTree::from(msg);
            ts.extend(once(msg))
        });
        out.extend(once(msg_paren));

        out
    }
}

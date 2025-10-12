use std::iter::once;

use crate::used_proc_macro::{Literal, Span, TokenTree, TokenStream};

use crate::utils::CrateToken;


#[derive(Debug)]
pub(crate) struct Error {
    span: Span,
    error: String,
}

impl Error {
    pub(crate) fn new(span: Span, error: impl Into<String>) -> Self {
        Self {
            span,
            error: error.into(),
        }
    }

    pub(crate) fn to_compile_error(&self, krate: CrateToken) -> TokenStream {
        let Error { ref error, span } = *self;

        let mut out = TokenStream::new();

        let krate = krate.krate.clone()
            .into_iter()
            .map(|mut k| {
                k.set_span(k.span().located_at(Span::call_site()));
                k
            });

        out.extend(krate);
        out.extend(crate::utils::colon2_token(span));
        out.extend(crate::utils::ident_token("__", span));
        out.extend(crate::utils::colon2_token(span));

        out.extend(crate::utils::ident_token("compile_error", span));

        out.extend(crate::utils::punct_token('!', span));

        let msg_paren = crate::utils::paren(span, |ts| {
            let mut msg = Literal::string(&error);
            msg.set_span(span);
            let msg = TokenTree::from(msg);
            ts.extend(once(msg))
        });
        out.extend(once(msg_paren));

        out
    }
}

use crate::{
    i129::I129,
    used_proc_macro::{Delimiter, Span, TokenTree, TokenStream},
    error::Error,
};


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnevaledExpr(pub(crate) String);


impl UnevaledExpr {
    pub fn new(ts: TokenStream) -> Self {
        let mut out = String::new();
        Self::new_inner(&mut out, ts);
        Self(out)
    }

    pub(crate) fn as_str(&self) -> &str {
        &self.0
    }

    fn new_inner(out: &mut String, ts: TokenStream) {
        for tt in ts {
            match &tt {
                TokenTree::Literal(lit) => {
                    let unparsed = lit.to_string();
                    out.push_str(&match parse_i129(lit.span(), &unparsed) {
                        Ok(x) => x.to_string(),
                        Err(_) => unparsed,
                    });
                }
                TokenTree::Group(group) => {
                    let (open, close) = match group.delimiter() {
                        Delimiter::Parenthesis => ('(', ')'),
                        Delimiter::Brace => ('{', '}'),
                        Delimiter::Bracket => ('[', ']'),
                        Delimiter::None => ('\0', '\0'),
                    };

                    out.push(open);
                    Self::new_inner(out, group.stream());
                    out.push(close);
                }
                TokenTree::Ident(ident)  => {
                    out.push_str(ident.to_string().trim_start_matches("r#"));
                }
                TokenTree::Punct(p) => {
                    // not taking spacing into account because proc_macro uses
                    // Spacing::Joint for unspaced angle brackets (used by generic params),
                    // which would make differences in formatting create unequal `UnevaledExpr`s
                    // if Spacing was taking into account.
                    out.push(p.as_char());
                }
            }
            if !matches!(tt, TokenTree::Punct(_)) {
                out.push(' ');
            }
        }
    }
}



pub fn parse_i129(span: Span, mut str: &str) -> Result<I129, Error> {
    let base;
    (base, str) = if let Some(stripped) = str.strip_prefix("0b") {
        (2, stripped)
    } else if let Some(stripped) = str.strip_prefix("0o") {
        (8, stripped)
    } else if let Some(stripped) = str.strip_prefix("0x") {
        (16, stripped)
    } else {
        (10, str)
    };

    if let Some((x, _)) = str.split_once(|c: char| matches!(c, 'g'..='z' | 'G'..='Z')) {
        str = x;
    }

    I129::from_str_radix(&str.trim().replace("_", ""), base)
        .map_err(|_| Error::new(span, "could not parse as integer"))
}





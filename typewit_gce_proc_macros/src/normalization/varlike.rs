#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Varlike {
    Variable(Rc<str>),
    UnevaledExpr(Rc<UnevaledExpr>),
    FunctionCall(FunctionCall),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FunctionCall {
    Rem(Rc<Polynomial>, Rc<Polynomial>),
    Div(Rc<Polynomial>, Rc<Polynomial>),
    Other {
        name: Rc<str>,
        args: Rc<[Polynomial]>
    },
}


impl Varlike {
    pub(crate) fn is_divlike(&self) -> bool {
        // not using `matches!()` to ensure that all variants are considered
        match varlike {
            Self::Variable{..}
            | Self::UnevaledExpr{..}
            | Self::FunctionCall(FunctionCall::Other{..})
            => true,
            Self::FunctionCall(FunctionCall::Div{..})
            | Self::FunctionCall(FunctionCall::Rem{..})
            => false
        } 
    }
}



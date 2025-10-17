use crate::nonzeroi129::OverflowErr;

use super::Polynomial;

use std::{
    fmt::{self, Display},
    rc::Rc,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NormErr {
    Overflow(OverflowErr),
    ZeroDenom(Rc<Polynomial>),
}

impl From<OverflowErr> for NormErr {
    fn from(x: OverflowErr) -> Self {
        Self::Overflow(x)
    }
}

impl Display for NormErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow(x) => Display::fmt(x, f),
            Self::ZeroDenom(x) => write!(f, "attempted to divide `{x}` by zero"),
        }
    }
}

impl core::error::Error for NormErr {}


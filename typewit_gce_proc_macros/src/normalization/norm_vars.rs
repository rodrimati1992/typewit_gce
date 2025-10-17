use crate::{
    unevaled_expr::UnevaledExpr,
    nonzeroi129::OverflowErr,
};

use super::{NormErr, Polynomial};

use std::{
    collections::btree_map::{BTreeMap, Entry as MapEntry},
    num::NonZeroU128,
    rc::Rc,
};



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
        match self {
            Self::Variable{..}
            | Self::UnevaledExpr{..}
            | Self::FunctionCall(FunctionCall::Other{..})
            => false,
            Self::FunctionCall(FunctionCall::Div{..})
            | Self::FunctionCall(FunctionCall::Rem{..})
            => true
        } 
    }
}


/////////////////////////////////////////


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Vars {
    vars: BTreeMap<Varlike, Power>,
}

pub(crate) type Power = NonZeroU128;

pub(crate) const POW1: Power = Power::new(1).unwrap();


impl Vars {
    pub(crate) fn new() -> Self {
        Self {
            vars: BTreeMap::new(),
        }
    }

    pub(crate) fn vars(&self) -> &BTreeMap<Varlike, Power> {
        &self.vars
    }

    pub(crate) fn insert_var(&mut self, var: Varlike, pow: Power) -> Result<(), NormErr> {
        match self.vars.entry(var) {
            MapEntry::Vacant(en) => _ = en.insert(pow),
            MapEntry::Occupied(en) => {
                match { en.get().checked_add(pow.get()) } {
                    Some(res) => *en.into_mut() = res,
                    None => {
                        let err = OverflowErr::new((*en.get()).into(), &"+", pow.into());
                        return Err(NormErr::Overflow(err))
                    }
                }
            }
        }
        Ok(())
    }

    /// 
    /// # Requirements
    /// 
    /// The iterator must be in order from lower to higher Varlike
    /// 
    /// # Panics
    /// 
    /// Panics if the power passed for any variable that is greater than is present.
    /// 
    pub(crate) fn remove_vars<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (Varlike, Power)>
    {
        let mut iter = iter.into_iter().peekable();

        let mut r_pow = POW1;
        self.vars.extract_if(.., |var, pow| {
            match iter.peek()  {
                Some((r_var, x)) if var == r_var => {
                    r_pow = *x;
                    _ = iter.next();
                }
                _ => return false
            }

            match Power::new(pow.get().strict_sub(r_pow.get())) {
                Some(res) => { *pow = res; false }
                None => true,
            }
        }).for_each(drop);
    }
}

#[cfg(test)]
impl std::iter::FromIterator<(Varlike, Power)> for Vars {
    fn from_iter<T>(iter: T) -> Self
    where 
        T: IntoIterator<Item = (Varlike, Power)>
    {
        let mut this = Self::new();
        for (var, pow) in iter {
            this.insert_var(var, pow).unwrap();
        }
        this
    }
}

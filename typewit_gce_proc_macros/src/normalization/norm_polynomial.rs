use crate::nonzeroi129::{IntErr, NonZeroI129};

use super::{
    norm_err::NormErr,
    norm_vars::Vars,
};

use std::collections::btree_map::{BTreeMap, Entry as MapEntry};



#[derive(Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Polynomial {
    pub(crate) terms: BTreeMap<Vars, Coefficient>,
}

pub(crate) type Coefficient = NonZeroI129;


impl Polynomial {
    pub(crate) fn zero() -> Self {
        Self {
            terms: Default::default(),
        }
    }

    pub(crate) fn terms(&self) -> &BTreeMap<Vars, Coefficient> {
        &self.terms
    }
    pub(crate) fn into_terms(self) -> impl Iterator<Item = (Vars, Coefficient)> {
        self.terms.into_iter()
    }

    pub(crate) fn insert_term(&mut self, term: impl Into<Term>) -> Result<(), NormErr> {
        let term: Term = term.into();
        match self.terms.entry(term.vars) {
            MapEntry::Vacant(en) => _ = en.insert(term.coeff),
            MapEntry::Occupied(en) => match { en.get().try_add(term.coeff) } {
                Ok(res) => *en.into_mut() = res,
                Err(IntErr::IsZero) => _ = en.remove(),
                Err(IntErr::Overflow(x)) => return Err(NormErr::Overflow(x)),
            },
        }
        Ok(())
    }

    /// # Requirements
    /// 
    /// The iterator must be in order from lower to higher Vars
    ///     
    pub(crate) fn remove_terms<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Vars>
    {
        let mut iter = iter.into_iter().peekable();

        self.terms.extract_if(.., |vars, _| {
            match iter.peek()  {
                Some(r_vars) if vars == r_vars => {
                    _ = iter.next();
                    true
                }
                _ => false
            }
        }).for_each(drop);
    }

    pub(crate) fn mul_assign_term(&mut self, rhs: &Term) -> Result<(), NormErr> {
        for (vars, coeff) in std::mem::take(&mut self.terms) {
            let mut term = Term { vars, coeff };
            term.mul_assign_term(rhs)?;
            self.insert_term(term)?;
        }
        Ok(())
    }
}

impl std::iter::FromIterator<(Vars, Coefficient)> for Polynomial {
    fn from_iter<T>(iter: T) -> Self
    where 
        T: IntoIterator<Item = (Vars, Coefficient)>
    {
        let mut this = Self::zero();
        for (vars, coeff) in iter {
            this.insert_term((vars, coeff)).unwrap();
        }
        this
    }
}


///////////////////////////////////////////////////


#[derive(Debug)]
pub(crate) struct Term {
    pub(crate) vars: Vars,
    pub(crate) coeff: Coefficient,
}

impl From<(Vars, Coefficient)> for Term {
    fn from((vars, coeff): (Vars, Coefficient)) -> Term {
        Term { vars, coeff }
    }
}

impl Term {
    pub(crate) fn mul_assign_term(&mut self, rhs: &Term) -> Result<(), NormErr> {
        for (rhs_var, rhs_pow) in rhs.vars.vars() {
            self.vars.insert_var(rhs_var.clone(), *rhs_pow)?;
        }

        self.coeff = self.coeff.try_mul(rhs.coeff)?;

        Ok(())
    }
}


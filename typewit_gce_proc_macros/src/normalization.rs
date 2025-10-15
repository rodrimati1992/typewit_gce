use crate::{
    i129::Sign,
    parsing_unnorm_polynomial::{
        UnnormPolynomial,
        UnnormPolynomialTerm,
        UnnormMulExpr,
        UnnormFunctionCall,
    },
    nonzeroi129::{IsZeroOk, OverflowErr, IntErr, NonZeroI129},
    unevaled_expr::UnevaledExpr,
    SimplifyFraction,
};

use std::{
    collections::btree_map::{BTreeMap, Entry as MapEntry},
    fmt::{self, Display},
    num::NonZeroU128,
    rc::Rc,
};

#[cfg(test)]
mod formatting_tests;

#[cfg(test)]
mod normal_tests;

#[cfg(test)]
mod div_rem_tests;

#[cfg(test)]
mod test_interpreter;

mod formatting;


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Polynomial {
    pub(crate) terms: Terms,
}

impl Polynomial {
    fn zero() -> Self {
        Self {
            terms: Terms::new(),
        }
    }
}

type Terms = BTreeMap<Vars, Coefficient>;
type Vars = BTreeMap<Varlike, Power>;
type Coefficient = NonZeroI129;
type Power = NonZeroU128;

const POW1: Power = Power::new(1).unwrap();

#[derive(Debug)]
struct Term {
    vars: Vars,
    coeff: Coefficient,
}

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



////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NormErr {
    Overflow,
    ZeroDenom,
}

impl From<OverflowErr> for NormErr {
    fn from(_: OverflowErr) -> Self {
        Self::Overflow
    }
}

impl Display for NormErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match *self {
            Self::Overflow => "numeric overflow",
            Self::ZeroDenom => "encountered zero denominator",
        })
    }
}

impl core::error::Error for NormErr {}


////////////////////////////////////////////////////////////////////



pub(crate) fn normalize_polynomial(
    upoly: UnnormPolynomial, 
    reduce_fractions: SimplifyFraction,
) -> Result<Polynomial, NormErr> {
    let mut poly = Polynomial::zero();

    for term in upoly.terms {
        normalize_term(term, reduce_fractions, &mut poly)?;
    }

    Ok(poly)
}


struct RemoveTerm {
    remove_term: bool
}


// normalizes one polynomial term, outputting its expanded polynomials to `out`
fn normalize_term(
    upoly: UnnormPolynomialTerm, 
    reduce_fractions: SimplifyFraction,
    out: &mut Polynomial,
) -> Result<(), NormErr> {
    let mut coefficient = Coefficient::one();
    let mut var_fns = BTreeMap::<Varlike, Power>::new();
    let mut norm_sub = Vec::<Polynomial>::new();

    if unexpanded_normalize_term (
        &mut coefficient, 
        &mut var_fns, 
        &mut norm_sub, 
        reduce_fractions, 
        upoly,
    )?.remove_term {
        return Ok(())
    }


    let mut accum_poly = Polynomial {
        terms: BTreeMap::from([(var_fns, coefficient)]),
    };

    for subpoly in norm_sub.into_iter() {
        let mut new_accum_poly = Polynomial::zero();

        for (l_var_fns, l_coef) in subpoly.terms {
            for (r_var_fns, r_coef) in accum_poly.terms
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())) 
            {
                let mut l_var_fns = l_var_fns.clone();

                for (r_var_fn, r_power) in r_var_fns {
                    insert_var(&mut l_var_fns, r_var_fn, r_power)?;
                }
            
                insert_term(&mut new_accum_poly, l_var_fns, l_coef.try_mul(r_coef)?)?;
            }
        }

        accum_poly = new_accum_poly;
    }

    for (vars, coeff) in accum_poly.terms {
        insert_term(out, vars, coeff)?;
    }

    Ok(())
}

fn unexpanded_normalize_term(
    coefficient: &mut NonZeroI129,
    var_fns: &mut BTreeMap<Varlike, Power>,
    norm_sub: &mut Vec<Polynomial>,
    reduce_fractions: SimplifyFraction,
    upoly: UnnormPolynomialTerm, 
) -> Result<RemoveTerm, NormErr> {
    let mut remove_term = false;

    'sube: for sube in upoly.mul_exprs {
        macro_rules! try_nz {
            ($e:expr) => (
                match $e.map_err(IntErr::from) {
                    Ok(x) => x,
                    Err(IntErr::IsZero) => {
                        // doesn't return immediately to detect normalization errors 
                        // in the remaining UnnormMulExprs
                        remove_term = true;
                        continue 'sube
                    },
                    Err(IntErr::Overflow) => return Err(NormErr::Overflow),
                }
            )
        }

        match sube {
            UnnormMulExpr::Constant(mulled_over) => {
                let mo = try_nz!(Coefficient::try_from(mulled_over));

                *coefficient = try_nz!(coefficient.try_mul(mo));
            }
            UnnormMulExpr::Variable(var) => {
                insert_var(var_fns, Varlike::Variable(var.into()), POW1)?;
            }
            UnnormMulExpr::UnevaledExpr(expr) => {
                insert_var(var_fns, Varlike::UnevaledExpr(expr.into()), POW1)?;
            }
            UnnormMulExpr::FunctionCall(func) => {
                use Varlike::FunctionCall as V_FC;

                let key = match func {
                    UnnormFunctionCall::Rem(numer, denom) => {
                        match normalize_rem(numer, denom, reduce_fractions)? {
                            NormalizedRemainder::Remainder(numer_out, denom_out, sign) => {
                                *coefficient = coefficient.with_sign(sign);
                                V_FC(FunctionCall::Rem(numer_out, denom_out))
                            }
                            NormalizedRemainder::Integer(None) => {
                                remove_term = true;
                                continue 'sube;
                            }
                            NormalizedRemainder::Integer(Some(int)) => {
                                *coefficient = try_nz!(coefficient.try_mul(int));
                                continue 'sube;
                            }
                        }
                    }
                    UnnormFunctionCall::Div(numer, denom) => {
                        match normalize_div(numer, denom, reduce_fractions)? {
                            NormalizedDivision::Division(numer_out, denom_out, sign) => {
                                *coefficient = coefficient.with_sign(sign);
                                V_FC(FunctionCall::Div(numer_out, denom_out))
                            }
                            NormalizedDivision::Polynomial(poly) => {
                                norm_sub.push(poly);
                                continue 'sube;
                            }
                            NormalizedDivision::Integer(None) => {
                                remove_term = true;
                                continue 'sube;
                            }
                            NormalizedDivision::Integer(Some(int)) => {
                                *coefficient = try_nz!(coefficient.try_mul(int));
                                continue 'sube;
                            }
                        }
                    }
                    UnnormFunctionCall::Other { name, args } => {
                        V_FC(FunctionCall::Other {
                            name: name.into(),
                            args: args.into_iter()
                                .map(|x| normalize_polynomial(x, reduce_fractions))
                                .collect::<Result<Vec<_>, _>>()?
                                .into(),
                        })
                    }
                };

                insert_var(var_fns, key, POW1)?
            }
            UnnormMulExpr::Parenthesis(paren) => {
                norm_sub.push(normalize_polynomial(paren, reduce_fractions)?)
            }
        }
    }

    Ok(RemoveTerm { remove_term })
}


enum NormalizedRemainder {
    Remainder(Rc<Polynomial>, Rc<Polynomial>, Sign),
    Integer(Option<NonZeroI129>),
}

fn normalize_rem(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
) -> Result<NormalizedRemainder, NormErr> {
    let (numer_poly, denom_poly, sign) = normalize_fraction(
        numerator, 
        denominator, 
        reduce_fractions, 
        |sign_numer, _| sign_numer, 
        |_, _| Ok(()),
    )?;

    if reduce_fractions.is_yes() {
        match (map_as_one_entry(&numer_poly.terms), map_as_one_entry(&denom_poly.terms)) {
            (Some((_, numer_coeff)), _) if *numer_coeff == 0 => {
                return Ok(NormalizedRemainder::Integer(None))
            }
            (_, Some((denom_vars, denom_coeff))) 
            if *denom_coeff == 1 && denom_vars.is_empty() 
            => {
                return Ok(NormalizedRemainder::Integer(None))
            }
            _ if numer_poly.terms.is_empty() => {
                return Ok(NormalizedRemainder::Integer(None))
            }
            (Some((numer_vars, numer_coeff)), Some((denom_vars, denom_coeff))) 
            if numer_vars.is_empty() && denom_vars.is_empty()
            => {
                return Ok(NormalizedRemainder::Integer(
                    numer_coeff
                        .try_rem(*denom_coeff)
                        .is_zero_ok()
                        .map(|x| x.with_sign(sign))
                ))
            }
            _ => {}
        }
    }

    Ok(NormalizedRemainder::Remainder(Rc::new(numer_poly), Rc::new(denom_poly), sign))
}


fn normalize_fraction(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
    map_sign: impl Fn(Sign, Sign) -> Sign,
    mut on_simplified_to_int: impl FnMut(Vars, Coefficient) -> Result<(), NormErr>
) -> Result<(Polynomial, Polynomial, Sign), NormErr> {
    let mut numer_poly = Polynomial::zero();
    let mut denom_poly = Polynomial::zero();

    normalize_term(numerator, reduce_fractions, &mut numer_poly)?;
    normalize_term(denominator, reduce_fractions, &mut denom_poly)?;

    // division by zero!
    if denom_poly.terms.is_empty() {
        return Err(NormErr::ZeroDenom);
    }

    let mut sign_out = Sign::Pos;

    if reduce_fractions.is_yes() {        
        if let Some((denom_term, denom_coeff)) = denom_poly.terms.iter().next()
        && denom_poly.terms.len() == 1 
        {
            let err = std::cell::Cell::new(None);
            for _ in numer_poly.terms.extract_if(.., |numer_vars, numer_coeff| {
                if let Some(Term { vars: out_vars, coeff: out_coeff }) = 
                    div_term_evenly((numer_vars, numer_coeff), (denom_term, denom_coeff))
                {
                    assert!(
                        err.replace(on_simplified_to_int(out_vars, out_coeff).err())
                            .is_none()
                    );
                    true
                } else {
                    false
                }
            }) {
                if let Some(e) = err.take() {
                    return Err(e);
                }
            }
        }

        let mut fact_numer = extract_common_factor(&mut numer_poly)?;
        let mut fact_denom = extract_common_factor(&mut denom_poly)?;
        
        (fact_numer, fact_denom) = div_term(fact_numer, fact_denom);

        {
            sign_out = map_sign(fact_numer.coeff.sign(), fact_denom.coeff.sign());

            fact_numer.coeff = fact_numer.coeff.abs();
            fact_denom.coeff = fact_denom.coeff.abs();
        }

        mul_assign_poly_with_term(&mut numer_poly, &fact_numer)?;
        mul_assign_poly_with_term(&mut denom_poly, &fact_denom)?;
    }

    Ok((numer_poly, denom_poly, sign_out))
}

struct IntegerDivision(Option<NonZeroI129>);

enum NormalizedDivision {
    Division(Rc<Polynomial>, Rc<Polynomial>, Sign),
    Polynomial(Polynomial),
    Integer(Option<NonZeroI129>),
}

fn normalize_div(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
) -> Result<NormalizedDivision, NormErr> {
    let mut out_poly = Polynomial::zero();

    let (numer_poly, denom_poly, sign) = normalize_fraction(
        numerator,
        denominator,
        reduce_fractions,
        |sign_numer, sign_denom| sign_numer * sign_denom,
        |out_vars, out_coeff| insert_term(&mut out_poly, out_vars, out_coeff)
    )?;

    if reduce_fractions.is_no() {
        return Ok(NormalizedDivision::Division(numer_poly.into(), denom_poly.into(), Sign::Pos))
    }

    let integer_div = match (
        map_as_one_entry(&numer_poly.terms), 
        map_as_one_entry(&denom_poly.terms)
    ) {
        (Some((_, numer_coeff)), _) if *numer_coeff == 0 => {
            Some(IntegerDivision(None))
        }
        _ if numer_poly.terms.is_empty() => {
            Some(IntegerDivision(None))
        }
        (Some((numer_vars, numer_coeff)), Some((denom_vars, denom_coeff))) 
        if numer_vars.is_empty() && denom_vars.is_empty()
        => {
            Some(IntegerDivision(
                numer_coeff
                    .try_div(*denom_coeff)
                    .is_zero_ok()
                    .map(|x| x.with_sign(sign))
            ))
        }
        (Some((numer_vars, numer_coeff)), Some((_, denom_coeff))) 
        if numer_vars.is_empty() && numer_coeff.magnitude() < denom_coeff.magnitude()
        => {
            Some(IntegerDivision(None))
        }
        _ => {
            None
        }
    };

    match (out_poly.terms.len(), integer_div) {
        (0, None) => Ok(NormalizedDivision::Division(numer_poly.into(), denom_poly.into(), sign)),
        (0, Some(IntegerDivision(n))) => {
            Ok(NormalizedDivision::Integer(n))
        },
        (1.., None) => {
            let key = Varlike::FunctionCall(
                FunctionCall::Div(Rc::new(numer_poly), Rc::new(denom_poly.into()))
            );

            insert_term(&mut out_poly, Vars::from([(key, POW1)]), sign.into())?;

            Ok(NormalizedDivision::Polynomial(out_poly))
        }
        (1.., Some(IntegerDivision(n))) => {
            if let Some(n) = n {
                insert_term(&mut out_poly, Vars::new(), n)?;
            }

            Ok(NormalizedDivision::Polynomial(out_poly))
        }
    }
}


fn insert_term(
    poly: &mut Polynomial, 
    vars: BTreeMap<Varlike, Power>, 
    coeff: Coefficient,
) -> Result<(), NormErr> {
    match poly.terms.entry(vars) {
        MapEntry::Vacant(en) => _ = en.insert(coeff),
        MapEntry::Occupied(en) => match { en.get().try_add(coeff) } {
            Ok(res) => *en.into_mut() = res,
            Err(IntErr::IsZero) => _ = en.remove(),
            Err(IntErr::Overflow) => return Err(NormErr::Overflow),
        },
    }
    Ok(())
}

fn insert_var(
    vars: &mut Vars, 
    var: Varlike, 
    pow: Power,
) -> Result<(), NormErr> {
    match vars.entry(var) {
        MapEntry::Vacant(en) => _ = en.insert(pow),
        MapEntry::Occupied(en) => {
            match { en.get().checked_add(pow.get()) } {
                Some(res) => *en.into_mut() = res,
                None => return Err(NormErr::Overflow),
            }
        }
    }
    Ok(())
}

fn mul_assign_poly_with_term(poly: &mut Polynomial, rhs: &Term) -> Result<(), NormErr> {
    for (vars, coeff) in std::mem::take(&mut poly.terms) {
        let mut term = Term { vars, coeff };
        mul_assign_term(&mut term, rhs)?;
        insert_term(poly, term.vars, term.coeff)?;
    }
    Ok(())
}

fn mul_assign_term(lhs: &mut Term, rhs: &Term) -> Result<(), NormErr> {
    for (rhs_var, rhs_pow) in &rhs.vars {
        insert_var(&mut lhs.vars, rhs_var.clone(), *rhs_pow)?;
    }

    lhs.coeff = lhs.coeff.try_mul(rhs.coeff)?;

    Ok(())
}

// returns a reduced fraction of numer/denom
fn div_term(mut numer: Term, mut denom: Term) -> (Term, Term) {
    numer.vars.extract_if(.., |numer_var, numer_pow| {
        if let MapEntry::Occupied(denom_pow_entry) = denom.vars.entry(numer_var.clone()) {
            let denom_pow = *denom_pow_entry.get();

            let min: Power = std::cmp::min(*numer_pow, denom_pow);

            match checked_sub_pow(denom_pow, min) {
                Some(res) => *denom_pow_entry.into_mut() = res,
                None => _ = denom_pow_entry.remove(),
            }
            match checked_sub_pow(*numer_pow, min) {
                Some(res) => { *numer_pow = res; false },
                None => true,
            }
        } else {
            false
        }
    }).for_each(drop);

    {
        let gcd = numer.coeff.gcd(denom.coeff);

        numer.coeff = numer.coeff.try_div(gcd).expect("/ gcd != 0 && gcd <= coeff");
        denom.coeff = denom.coeff.try_div(gcd).expect("/ gcd != 0 && gcd <= coeff");
    }

    (numer, denom)
}

// computes numer/denom, only returning the result if the remainder is zero
fn div_term_evenly(
    (numer_vars, numer_coeff): (&Vars, &Coefficient), 
    (denom_vars, denom_coeff): (&Vars, &Coefficient),
) -> Option<Term> {
    let mut out = if numer_coeff.is_multiple_of(*denom_coeff) {
        Term {
            vars: BTreeMap::new(),
            coeff: numer_coeff.try_div(*denom_coeff)
                .expect("division of multiple shouldn't return 0 or overflow"),
        }
    } else {
        return None
    };

    if denom_vars.keys().any(|denom_var| !numer_vars.contains_key(denom_var)) {
        return None;
    }

    for (numer_var, mut numer_pow) in numer_vars.iter().map(|(k, v)| (k.clone(), v.clone())) {
        if let Some(denom_pow) = denom_vars.get(&numer_var) {
            match Power::new(numer_pow.get().checked_sub(denom_pow.get())?) {
                Some(subbed) => numer_pow = subbed,
                None => continue,
            }
        }
        out.vars.insert(numer_var, numer_pow);
    }

    Some(out)
}

fn extract_common_factor(poly: &mut Polynomial) -> Result<Term, NormErr> {
    let fact = find_common_factor(poly);

    for (vars, coeff) in std::mem::take(&mut poly.terms) {
        let term = div_term_evenly((&vars, &coeff), (&fact.vars, &fact.coeff))
            .expect("coeff and vars must be a multiple of fact, due to how fact is computed");

        insert_term(poly, term.vars, term.coeff)?;
    }

    Ok(fact)
}

fn find_common_factor(poly: &Polynomial) -> Term {
    let mut iter = poly.terms.iter();

    let Some((mut accum_vars, mut accum_coef)) = iter.next().map(|(k, v)| (k.clone(), v.clone()))
    else {        
        return Term {
            vars: Vars::new(),
            coeff: Coefficient::one(),
        }
    };
    
    if poly.terms.len() == 1 {
        return Term {
            vars: accum_vars,
            coeff: accum_coef,
        }
    }

    for (vars, coef) in iter {
        accum_coef = coef.gcd(accum_coef);

        accum_vars.extract_if(.., |accum_var, accum_pow|{
            if let Some(pow) = vars.get(accum_var) {
                assign_min(accum_pow, pow);
                false
            } else {
                // remove, because this variable isn't a common factor with this term
                true 
            }
        }).for_each(drop);
    }

    Term {
        vars: accum_vars,
        coeff: accum_coef,
    }
}




fn assign_min<T: std::cmp::Ord + Clone>(l: &mut T, r: &T) {
    if *l > *r {
        *l = r.clone();
    }
}

fn map_as_one_entry<K, V>(map: &BTreeMap<K, V>) -> Option<(&K, &V)> {
    if map.len() == 1 {
        map.iter().next()
    } else {
        None
    }
}

fn not_divlike(varlike: &Varlike) -> bool {
    use Varlike as Vl;
    use FunctionCall as FC;

    // not using `matches!()` to ensure that all variants are considered
    match varlike {
        Vl::Variable{..}
        | Vl::UnevaledExpr{..}
        | Vl::FunctionCall(FC::Other{..})
        => true,
        Vl::FunctionCall(FC::Div{..})
        | Vl::FunctionCall(FC::Rem{..})
        => false
    } 
}

fn polynomial_is_unparenth_numer(poly: &Polynomial) -> bool {
    poly.terms.len() == 0 || 
    map_as_one_entry(&poly.terms).is_some_and(|(vars, _)| {
        vars.iter().all(|(varlike, _power)| not_divlike(varlike))
    })
}

fn polynomial_is_unparenth_denom(poly: &Polynomial) -> bool {
    poly.terms.len() == 0 || 
    map_as_one_entry(&poly.terms).is_some_and(|(vars, coeff)| {
        vars.len() == 0 || 
        *coeff == 1 &&
        map_as_one_entry(vars).is_some_and(|(varlike, _power)| not_divlike(varlike))
    })
}


fn checked_sub_pow(lhs: Power, rhs: Power) -> Option<Power> {
    lhs.get()
        .checked_sub(rhs.get())
        .and_then(Power::new)
}

use crate::{
    i129::Sign,
    parsing_unnorm_polynomial::UnnormPolynomialTerm,
    nonzeroi129::{IsZeroOk, NonZeroI129},
    SimplifyFraction,
};

use super::{
    norm_err::NormErr,
    norm_polynomial::{Coefficient, Polynomial, Term},
    norm_vars::{POW1, Power, Vars, Varlike, FunctionCall},
    map_as_one_entry, normalize_term,
};

use std::rc::Rc;




pub(crate) enum NormalizedRemainder {
    Remainder(Rc<Polynomial>, Rc<Polynomial>, Sign),
    Integer(Option<NonZeroI129>),
}

pub(crate) fn normalize_rem(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
) -> Result<NormalizedRemainder, NormErr> {
    let (numer_poly, denom_poly, sign) = normalize_fraction(
        numerator, 
        denominator, 
        reduce_fractions, 
        |a, b| (a, b),
        |sign_numer, _| sign_numer, 
        |_, _| Ok(()),
    )?;

    if reduce_fractions.is_yes() {
        match (map_as_one_entry(numer_poly.terms()), map_as_one_entry(denom_poly.terms())) {
            // ... % 1
            (_, Some((denom_vars, denom_coeff))) 
            if *denom_coeff == 1 && denom_vars.vars().is_empty() 
            => {
                return Ok(NormalizedRemainder::Integer(None))
            }
            // 0 % ...
            _ if numer_poly.terms().is_empty() => {
                return Ok(NormalizedRemainder::Integer(None))
            }
            (Some((numer_vars, numer_coeff)), Some((denom_vars, denom_coeff))) 
            if numer_vars.vars().is_empty() && denom_vars.vars().is_empty()
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
    common_factor_divider: impl Fn(Term, Term) -> (Term, Term),
    map_sign: impl Fn(Sign, Sign) -> Sign,
    mut on_simplified_to_int: impl FnMut(Vars, Coefficient) -> Result<(), NormErr>
) -> Result<(Polynomial, Polynomial, Sign), NormErr> {
    let mut numer_poly = Polynomial::zero();
    let mut denom_poly = Polynomial::zero();

    normalize_term(numerator, reduce_fractions, &mut numer_poly)?;
    normalize_term(denominator, reduce_fractions, &mut denom_poly)?;

    // division by zero!
    if denom_poly.terms().is_empty() {
        return Err(NormErr::ZeroDenom(numer_poly.into()));
    }

    let mut sign_out = Sign::Pos;

    if reduce_fractions.is_yes() {        
        if let Some((denom_term, denom_coeff)) = denom_poly.terms().iter().next()
        && denom_poly.terms().len() == 1 
        {
            let mut to_remove = Vec::<Vars>::new();

            for (numer_vars, numer_coeff) in numer_poly.terms() {
                if let Some(Term { vars: out_vars, coeff: out_coeff }) = 
                    div_term_evenly((numer_vars, numer_coeff), (denom_term, denom_coeff))
                {
                    on_simplified_to_int(out_vars, out_coeff)?;

                    to_remove.push(numer_vars.clone());
                }
            }

            numer_poly.remove_terms(to_remove);
        }

        let mut fact_numer = extract_common_factor(&mut numer_poly)?;
        let mut fact_denom = extract_common_factor(&mut denom_poly)?;
        
        (fact_numer, fact_denom) = common_factor_divider(fact_numer, fact_denom);

        {
            sign_out = map_sign(fact_numer.coeff.sign(), fact_denom.coeff.sign());

            fact_numer.coeff = fact_numer.coeff.abs();
            fact_denom.coeff = fact_denom.coeff.abs();
        }

        numer_poly.mul_assign_term(&fact_numer)?;
        denom_poly.mul_assign_term(&fact_denom)?;
    }

    Ok((numer_poly, denom_poly, sign_out))
}



pub(crate) struct IntegerDivision(Option<NonZeroI129>);

pub(crate) enum NormalizedDivision {
    Division(Rc<Polynomial>, Rc<Polynomial>, Sign),
    Polynomial(Polynomial),
    Integer(Option<NonZeroI129>),
}

pub(crate) fn normalize_div(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
) -> Result<NormalizedDivision, NormErr> {
    let mut out_poly = Polynomial::zero();

    let (numer_poly, denom_poly, sign) = normalize_fraction(
        numerator,
        denominator,
        reduce_fractions,
        div_term,
        |sign_numer, sign_denom| sign_numer * sign_denom,
        |out_vars, out_coeff| out_poly.insert_term((out_vars, out_coeff))
    )?;

    if reduce_fractions.is_no() {
        return Ok(NormalizedDivision::Division(numer_poly.into(), denom_poly.into(), Sign::Pos))
    }

    let integer_div = match (
        map_as_one_entry(numer_poly.terms()), 
        map_as_one_entry(denom_poly.terms()),
    ) {
        // 0 / ...
        _ if numer_poly.terms().is_empty() => {
            Some(IntegerDivision(None))
        }
        (Some((numer_vars, numer_coeff)), Some((denom_vars, denom_coeff))) 
        if numer_vars.vars().is_empty() && denom_vars.vars().is_empty()
        => {
            Some(IntegerDivision(
                numer_coeff
                    .try_div(*denom_coeff)
                    .is_zero_ok()
                    .map(|x| x.with_sign(sign))
            ))
        }
        (Some((numer_vars, numer_coeff)), Some((_, denom_coeff))) 
        if numer_vars.vars().is_empty() && numer_coeff.magnitude() < denom_coeff.magnitude()
        => {
            Some(IntegerDivision(None))
        }
        _ => {
            None
        }
    };

    match (out_poly.terms().len(), integer_div) {
        (0, None) => Ok(NormalizedDivision::Division(numer_poly.into(), denom_poly.into(), sign)),
        (0, Some(IntegerDivision(n))) => {
            Ok(NormalizedDivision::Integer(n))
        },
        (1.., None) => {
            let key = Varlike::FunctionCall(
                FunctionCall::Div(Rc::new(numer_poly), Rc::new(denom_poly.into()))
            );

            out_poly.insert_term((Vars::from_iter([(key, POW1)]), sign.into()))?;

            Ok(NormalizedDivision::Polynomial(out_poly))
        }
        (1.., Some(IntegerDivision(n))) => {
            if let Some(n) = n {
                out_poly.insert_term((Vars::new(), n))?;
            }

            Ok(NormalizedDivision::Polynomial(out_poly))
        }
    }
}


// returns a reduced fraction of numer/denom
fn div_term(mut numer: Term, mut denom: Term) -> (Term, Term) {
    let to_remove: Vec<(Varlike, Power)> = numer.vars
        .vars()
        .iter()
        .filter_map(|(numer_var, numer_pow)| {
            denom.vars.vars().get(numer_var).map(move |denom_pow| {
                (numer_var.clone(), std::cmp::min(*numer_pow, *denom_pow))
            })
        })
        .collect();

    numer.vars.remove_vars(to_remove.iter().cloned());

    denom.vars.remove_vars(to_remove);

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
            vars: Vars::new(),
            coeff: numer_coeff.try_div(*denom_coeff)
                .expect("division of multiple shouldn't return 0 or overflow"),
        }
    } else {
        return None
    };

    if denom_vars.vars().keys().any(|denom_var| !numer_vars.vars().contains_key(denom_var)) {
        return None;
    }

    for (numer_var, mut numer_pow) in 
        numer_vars.vars().iter().map(|(k, v)| (k.clone(), v.clone()))
    {
        if let Some(denom_pow) = denom_vars.vars().get(&numer_var) {
            match Power::new(numer_pow.get().checked_sub(denom_pow.get())?) {
                Some(subbed) => numer_pow = subbed,
                None => continue,
            }
        }
        out.vars.insert_var(numer_var, numer_pow)
            .expect("coefficient can only go down WRT the args");
    }

    Some(out)
}

fn extract_common_factor(poly: &mut Polynomial) -> Result<Term, NormErr> {
    let fact = find_common_factor(poly);

    for (vars, coeff) in std::mem::take(poly).into_terms() {
        let term = div_term_evenly((&vars, &coeff), (&fact.vars, &fact.coeff))
            .expect("coeff and vars must be a multiple of fact, due to how fact is computed");

        poly.insert_term(term)?;
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

    let mut to_remove: Vec<(Varlike, Power)> = Vec::new();
    for (vars, coef) in iter {
        accum_coef = coef.gcd(accum_coef);

        to_remove.clear();
        to_remove.extend(
            accum_vars
            .vars()
            .iter()
            .filter_map(|(accum_var, accum_pow)| {
                let removed = match vars.vars().get(accum_var) {
                    Some(&pow) => sub_pow(*accum_pow, std::cmp::min(*accum_pow, pow))?,
                    None => *accum_pow,
                };
                
                Some((accum_var.clone(), removed))
            })
        );

        accum_vars.remove_vars(to_remove.drain(..));
    }

    Term {
        vars: accum_vars,
        coeff: accum_coef,
    }
}


fn sub_pow(lhs: Power, rhs: Power) -> Option<Power> {
    Power::new(lhs.get().strict_sub(rhs.get()))
}







use crate::{
    parsing_unnorm_polynomial::{
        UnnormPolynomial,
        UnnormPolynomialTerm,
        UnnormMulExpr,
        UnnormFunctionCall,
    },
    nonzeroi129::{IntErr, NonZeroI129},
    SimplifyFraction,
};

use std::collections::btree_map::BTreeMap;

#[cfg(test)]
mod formatting_tests;

#[cfg(test)]
mod normal_tests;

#[cfg(test)]
mod div_rem_tests;

#[cfg(test)]
mod test_interpreter;

mod formatting;

mod norm_err;

mod norm_polynomial;

mod norm_rem_div;

mod norm_vars;


#[allow(unused_imports)]
pub(crate) use self::{
    norm_err::NormErr,
    norm_polynomial::{Coefficient, Polynomial},
    norm_rem_div::{
        NormalizedDivision, NormalizedRemainder, 
        normalize_rem, normalize_div,
    },
    norm_vars::{POW1, Power, Vars, Varlike, FunctionCall},
};

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
    let mut var_fns = Vars::new();
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


    let mut accum_poly = Polynomial::zero();
    accum_poly.insert_term((var_fns, coefficient)).expect("was empty before, so can't overflow");

    for subpoly in norm_sub.into_iter() {
        let mut new_accum_poly = Polynomial::zero();

        for (l_var_fns, l_coef) in subpoly.terms() {
            for (r_var_fns, r_coef) in accum_poly.terms()
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())) 
            {
                let mut l_var_fns = l_var_fns.clone();

                for (r_var_fn, r_power) in r_var_fns.vars().iter() {
                    l_var_fns.insert_var(r_var_fn.clone(), *r_power)?;
                }
            
                new_accum_poly.insert_term((l_var_fns, l_coef.try_mul(r_coef)?))?;
            }
        }

        accum_poly = new_accum_poly;
    }

    for (vars, coeff) in accum_poly.into_terms() {
        out.insert_term((vars, coeff))?;
    }

    Ok(())
}

fn unexpanded_normalize_term(
    coefficient: &mut NonZeroI129,
    var_fns: &mut Vars,
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
                    Err(IntErr::Overflow(x)) => return Err(NormErr::Overflow(x)),
                }
            )
        }

        match sube {
            UnnormMulExpr::Constant(mulled_over) => {
                let mo = try_nz!(Coefficient::try_from(mulled_over));

                *coefficient = try_nz!(coefficient.try_mul(mo));
            }
            UnnormMulExpr::Variable(var) => {
                var_fns.insert_var(Varlike::Variable(var.into()), POW1)?;
            }
            UnnormMulExpr::UnevaledExpr(expr) => {
                var_fns.insert_var(Varlike::UnevaledExpr(expr.into()), POW1)?;
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

                var_fns.insert_var(key, POW1)?;
            }
            UnnormMulExpr::Parenthesis(paren) => {
                norm_sub.push(normalize_polynomial(paren, reduce_fractions)?)
            }
        }
    }

    Ok(RemoveTerm { remove_term })
}






fn map_as_one_entry<K, V>(map: &BTreeMap<K, V>) -> Option<(&K, &V)> {
    if map.len() == 1 {
        map.iter().next()
    } else {
        None
    }
}


fn polynomial_is_unparenth_numer(poly: &Polynomial) -> bool {
    poly.terms().len() == 0 || 
    map_as_one_entry(poly.terms()).is_some_and(|(vars, _)| {
        vars.vars().iter().all(|(varlike, _power)| !varlike.is_divlike())
    })
}

fn polynomial_is_unparenth_denom(poly: &Polynomial) -> bool {
    poly.terms().len() == 0 || 
    map_as_one_entry(poly.terms()).is_some_and(|(vars, coeff)| {
        vars.vars().len() == 0 || 
        *coeff == 1 &&
        map_as_one_entry(vars.vars()).is_some_and(|(varlike, _power)| !varlike.is_divlike())
    })
}


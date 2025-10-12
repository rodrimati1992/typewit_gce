use crate::{
    parsing_unnorm_polynomial::{
        UnnormPolynomial,
        UnnormPolynomialTerm,
        UnnormMulExpr,
        UnnormFunctionCall,
    },
    unevaled_expr::UnevaledExpr,
    utils::bi_eq,
    SimplifyFraction,
};

use num_bigint::{BigInt, BigUint, Sign};
use num_integer::Integer;
use num_traits::{CheckedSub, Signed};


use std::{
    collections::{
        btree_map::{BTreeMap, Entry as MapEntry},
        btree_set::BTreeSet,
    },
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
type Coefficient = BigInt;
type Power = BigUint;

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





pub(crate) fn normalize_polynomial(
    upoly: UnnormPolynomial, 
    reduce_fractions: SimplifyFraction,
) -> Polynomial {
    let mut poly = Polynomial::zero();

    for term in upoly.terms {
        normalize_term(term, reduce_fractions, &mut poly);
    }

    // removing polynomial terms of zero coefficient.
    {
        let mut zeroed_out = BTreeSet::new();
        for (vars, coeff) in poly.terms.iter() {
            #[cfg(test)]
            for (var, pow) in vars {
                assert_ne!(*pow, BigUint::ZERO, "{var:?}");
            }

            if *coeff == BigInt::ZERO {
                zeroed_out.insert(vars.clone());
            }
        }

        for removed in zeroed_out {
            poly.terms.remove(&removed);
        }
    }

    poly
}


// normalizes one polynomial term, outputting its expanded polynomials to `out`
fn normalize_term(
    upoly: UnnormPolynomialTerm, 
    reduce_fractions: SimplifyFraction,
    out: &mut Polynomial,
) {
    let mut coefficient = BigInt::from(1);
    let mut var_fns = BTreeMap::<Varlike, Power>::new();
    let mut norm_sub = Vec::<Polynomial>::new();

    unexpanded_normalize_term(
        &mut coefficient, 
        &mut var_fns, 
        &mut norm_sub, 
        reduce_fractions, 
        upoly,
    );

    if coefficient == BigInt::ZERO {
        return
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
                    match l_var_fns.entry(r_var_fn) {
                        MapEntry::Vacant(en) => _ = en.insert(r_power),
                        MapEntry::Occupied(en) => *en.into_mut() += r_power,
                    }
                }
            
                insert_term(&mut new_accum_poly, l_var_fns, (&l_coef) * r_coef)
            }
        }

        accum_poly = new_accum_poly;
    }

    for (vars, coeff) in accum_poly.terms {
        insert_term(out, vars, coeff)
    }
}

fn unexpanded_normalize_term(
    coefficient: &mut BigInt,
    var_fns: &mut BTreeMap<Varlike, Power>,
    norm_sub: &mut Vec<Polynomial>,
    reduce_fractions: SimplifyFraction,
    upoly: UnnormPolynomialTerm, 
) {
    'sube: for sube in upoly.mul_exprs {
        match sube {
            UnnormMulExpr::Constant(mulled_over) => {
                *coefficient *= mulled_over;
            }
            UnnormMulExpr::Variable(var) => {
                match var_fns.entry(Varlike::Variable(var.into())) {
                    MapEntry::Vacant(en) => _ = en.insert(1u8.into()),
                    MapEntry::Occupied(en) => *en.into_mut() += 1u8,
                }
            }
            UnnormMulExpr::UnevaledExpr(expr) => {
                match var_fns.entry(Varlike::UnevaledExpr(expr.into())) {
                    MapEntry::Vacant(en) => _ = en.insert(1u8.into()),
                    MapEntry::Occupied(en) => *en.into_mut() += 1u8,
                }
            }
            UnnormMulExpr::FunctionCall(func) => {
                use Varlike::FunctionCall as V_FC;

                let key = match func {
                    UnnormFunctionCall::Rem(numer, denom) => {
                        match normalize_rem(numer, denom, reduce_fractions) {
                            NormalizedRemainder::Remainder(numer_out, denom_out, sign_i8) => {
                                *coefficient *= sign_i8;
                                V_FC(FunctionCall::Rem(numer_out, denom_out))
                            }
                            NormalizedRemainder::Integer(int) => {
                                *coefficient *= int;
                                continue 'sube;
                            }
                        }
                    }
                    UnnormFunctionCall::Div(numer, denom) => {
                        match normalize_div(numer, denom, reduce_fractions) {
                            NormalizedDivision::Division(numer_out, denom_out, sign_i8) => {
                                *coefficient *= sign_i8;
                                V_FC(FunctionCall::Div(numer_out, denom_out))
                            }
                            NormalizedDivision::Polynomial(poly) => {
                                norm_sub.push(poly);
                                continue 'sube;
                            }
                            NormalizedDivision::Integer(int) => {
                                *coefficient *= int;
                                continue 'sube;
                            }
                        }
                    }
                    UnnormFunctionCall::Other { name, args } => {
                        V_FC(FunctionCall::Other {
                            name: name.into(),
                            args: args.into_iter()
                                .map(|x| normalize_polynomial(x, reduce_fractions))
                                .collect(),
                        })
                    }
                };

                match var_fns.entry(key) {
                    MapEntry::Vacant(en) => _ = en.insert(1u8.into()),
                    MapEntry::Occupied(en) => *en.into_mut() += 1u8,
                }
            }
            UnnormMulExpr::Parenthesis(paren) => {
                norm_sub.push(normalize_polynomial(paren, reduce_fractions))
            }
        }
    }
}


enum NormalizedRemainder {
    Remainder(Rc<Polynomial>, Rc<Polynomial>, i8),
    Integer(BigInt),
}

fn normalize_rem(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
) -> NormalizedRemainder {
    let (numer_poly, denom_poly, sign_i8) = normalize_fraction(
        numerator, 
        denominator, 
        reduce_fractions, 
        |sign_numer, _| sign_numer, 
        |_, _| (),
    );

    if reduce_fractions.is_yes() {
        match (map_as_one_entry(&numer_poly.terms), map_as_one_entry(&denom_poly.terms)) {
            (Some((_, numer_coeff)), _) if bi_eq(numer_coeff, 0) => {
                return NormalizedRemainder::Integer(0.into())
            }
            (_, Some((denom_vars, denom_coeff))) 
            if bi_eq(denom_coeff, 1) && denom_vars.is_empty() 
            => {
                return NormalizedRemainder::Integer(0.into())
            }
            _ if numer_poly.terms.is_empty() => {
                return NormalizedRemainder::Integer(0.into())
            }
            (Some((numer_vars, numer_coeff)), Some((denom_vars, denom_coeff))) 
            if numer_vars.is_empty() && denom_vars.is_empty()
            => {
                return NormalizedRemainder::Integer((numer_coeff % denom_coeff) * sign_i8)
            }
            _ => {}
        }
    }

    NormalizedRemainder::Remainder(Rc::new(numer_poly), Rc::new(denom_poly), sign_i8)
}


fn normalize_fraction(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
    map_sign: impl Fn(Sign, Sign) -> Sign,
    mut on_simplified_to_int: impl FnMut(Vars, Coefficient)
) -> (Polynomial, Polynomial, i8) {
    let mut numer_poly = Polynomial::zero();
    let mut denom_poly = Polynomial::zero();

    normalize_term(numerator, reduce_fractions, &mut numer_poly);
    normalize_term(denominator, reduce_fractions, &mut denom_poly);

    let mut sign_out = 1;

    if reduce_fractions.is_yes() {        
        if denom_poly.terms.len() == 1 {
            let (denom_term, denom_coeff) = &denom_poly.terms.iter().next().unwrap();

            numer_poly.terms.extract_if(.., |numer_vars, numer_coeff| {
                if let Some(Term { vars: out_vars, coeff: out_coeff }) = 
                    div_term_evenly((numer_vars, numer_coeff), (denom_term, denom_coeff))
                {
                    on_simplified_to_int(out_vars, out_coeff);
                    true
                } else {
                    false
                }
            }).for_each(drop);
        }

        let mut fact_numer = extract_common_factor(&mut numer_poly);
        let mut fact_denom = extract_common_factor(&mut denom_poly);
        
        (fact_numer, fact_denom) = div_term(fact_numer, fact_denom);

        {
            let sign = map_sign(fact_numer.coeff.sign(), fact_denom.coeff.sign());

            sign_out = match sign {
                Sign::Minus => -1,
                _ => 1,
            };

            fact_numer.coeff = fact_numer.coeff.abs();
            fact_denom.coeff = fact_denom.coeff.abs();
        }

        mul_assign_poly_with_term(&mut numer_poly, &fact_numer);
        mul_assign_poly_with_term(&mut denom_poly, &fact_denom);
    }

    (numer_poly, denom_poly, sign_out)
}

struct IntegerDivision(BigInt);

enum NormalizedDivision {
    Division(Rc<Polynomial>, Rc<Polynomial>, i8),
    Polynomial(Polynomial),
    Integer(BigInt),
}

fn normalize_div(
    numerator: UnnormPolynomialTerm,
    denominator: UnnormPolynomialTerm,
    reduce_fractions: SimplifyFraction,
) -> NormalizedDivision {
    let mut out_poly = Polynomial::zero();

    let (numer_poly, denom_poly, sign_i8) = normalize_fraction(
        numerator,
        denominator,
        reduce_fractions,
        |sign_numer, sign_denom| sign_numer * sign_denom,
        |out_vars, out_coeff| insert_term(&mut out_poly, out_vars, out_coeff)
    );

    if reduce_fractions.is_no() {
        return NormalizedDivision::Division(numer_poly.into(), denom_poly.into(), 1)
    }

    let integer_div = match (
        map_as_one_entry(&numer_poly.terms), 
        map_as_one_entry(&denom_poly.terms)
    ) {
        (Some((_, numer_coeff)), _) if bi_eq(numer_coeff, 0) => {
            Some(IntegerDivision(0.into()))
        }
        _ if numer_poly.terms.is_empty() => {
            Some(IntegerDivision(0.into()))
        }
        (Some((numer_vars, numer_coeff)), Some((denom_vars, denom_coeff))) 
        if numer_vars.is_empty() && denom_vars.is_empty()
        => {
            Some(IntegerDivision((numer_coeff / denom_coeff) * sign_i8))
        }
        (Some((numer_vars, numer_coeff)), Some((_, denom_coeff))) 
        if numer_vars.is_empty() && numer_coeff.magnitude() < denom_coeff.magnitude()
        => {
            Some(IntegerDivision(0.into()))
        }
        _ => {
            None
        }
    };

    match (out_poly.terms.len(), integer_div) {
        (0, None) => NormalizedDivision::Division(numer_poly.into(), denom_poly.into(), sign_i8),
        (0, Some(IntegerDivision(n))) => NormalizedDivision::Integer(n),
        (1.., None) => {
            let key = Varlike::FunctionCall(
                FunctionCall::Div(Rc::new(numer_poly), Rc::new(denom_poly.into()))
            );

            insert_term(&mut out_poly, Vars::from([(key, 1u8.into())]), sign_i8.into());

            NormalizedDivision::Polynomial(out_poly)
        }
        (1.., Some(IntegerDivision(n))) => {
            if n != BigInt::ZERO {
                insert_term(&mut out_poly, Vars::new(), n.into());
            }

            NormalizedDivision::Polynomial(out_poly)
        }
    }
}


fn insert_term(poly: &mut Polynomial, vars: BTreeMap<Varlike, Power>, coeff: Coefficient) {
    match poly.terms.entry(vars) {
        MapEntry::Vacant(en) => _ = en.insert(coeff),
        MapEntry::Occupied(en) => *en.into_mut() += coeff,
    }
}

fn mul_assign_poly_with_term(poly: &mut Polynomial, rhs: &Term) {
    for (vars, coeff) in std::mem::take(&mut poly.terms) {
        let mut term = Term { vars, coeff };
        mul_assign_term(&mut term, rhs);
        insert_term(poly, term.vars, term.coeff)
    }
}

fn mul_assign_term(lhs: &mut Term, rhs: &Term) {
    for (rhs_var, rhs_pow) in &rhs.vars {
        match lhs.vars.entry(rhs_var.clone()) {
            MapEntry::Vacant(en) => _ = en.insert(rhs_pow.clone()),
            MapEntry::Occupied(en) => *en.into_mut() += &*rhs_pow,
        }
    }

    lhs.coeff *= &rhs.coeff;
}

// returns a reduced fraction of numer/denom
fn div_term(mut numer: Term, mut denom: Term) -> (Term, Term) {
    numer.vars.extract_if(.., |numer_var, numer_pow| {
        if let MapEntry::Occupied(mut denom_pow_entry) = denom.vars.entry(numer_var.clone()) {
            let denom_pow = denom_pow_entry.get_mut();
            let subbed: BigUint = (&*numer_pow).min(&*denom_pow).clone();

            *numer_pow -= subbed.clone();
            *denom_pow -= subbed;

            if *denom_pow == BigUint::ZERO {
                denom_pow_entry.remove();
            }

            *numer_pow == BigUint::ZERO
        } else {
            false
        }
    }).for_each(drop);

    {
        let gcd = (&numer.coeff).gcd(&denom.coeff);
        numer.coeff /= gcd.clone();
        denom.coeff /= gcd;
    }

    (numer, denom)
}

// computes numer/denom, only returning the result if the remainder is zero
fn div_term_evenly(
    (numer_vars, numer_coeff): (&Vars, &Coefficient), 
    (denom_vars, denom_coeff): (&Vars, &Coefficient),
) -> Option<Term> {
    let mut out = if numer_coeff.is_multiple_of(&denom_coeff) {
        Term {
            vars: BTreeMap::new(),
            coeff: numer_coeff / denom_coeff,
        }
    } else {
        return None
    };

    if denom_vars.keys().any(|denom_var| !numer_vars.contains_key(denom_var)) {
        return None;
    }

    for (numer_var, mut numer_pow) in numer_vars.iter().map(|(k, v)| (k.clone(), v.clone())) {
        if let Some(denom_pow) = denom_vars.get(&numer_var) {
            numer_pow = numer_pow.checked_sub(&denom_pow)?;
        }

        if numer_pow != BigUint::ZERO {
            out.vars.insert(numer_var, numer_pow);
        }
    }

    Some(out)
}

fn extract_common_factor(poly: &mut Polynomial) -> Term {
    let fact = find_common_factor(poly);

    for (vars, coeff) in std::mem::take(&mut poly.terms) {
        // coeff and vars must be a multiple of fact, due to how fact is computed
        let term = div_term_evenly((&vars, &coeff), (&fact.vars, &fact.coeff)).unwrap();
        insert_term(poly, term.vars, term.coeff);
    }

    fact
}

fn find_common_factor(poly: &Polynomial) -> Term {
    if poly.terms.is_empty() {
        return Term {
            vars: Vars::new(),
            coeff: BigInt::from(1),
        }
    }

    let mut iter = poly.terms.iter();
    let (mut accum_vars, mut accum_coef) = 
        iter.next().map(|(k, v)| (k.clone(), v.clone())).unwrap();
    
    if poly.terms.len() == 1 {
        return Term {
            vars: accum_vars,
            coeff: accum_coef,
        }
    }

    for (vars, coef) in iter {
        accum_coef = coef.gcd(&accum_coef);

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
    map_as_one_entry(&poly.terms).is_some_and(|(vars, coeff)| {
        vars.iter().all(|(varlike, _power)| not_divlike(varlike))
    })
}

fn polynomial_is_unparenth_denom(poly: &Polynomial) -> bool {
    poly.terms.len() == 0 || 
    map_as_one_entry(&poly.terms).is_some_and(|(vars, coeff)| {
        vars.len() == 0 || 
        crate::utils::bu_eq(coeff.magnitude(), 1) &&
        map_as_one_entry(vars).is_some_and(|(varlike, _power)| not_divlike(varlike))
    })
}



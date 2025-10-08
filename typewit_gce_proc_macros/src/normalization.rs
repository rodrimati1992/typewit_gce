use crate::parsing_unnorm_polynomial::{
    UnnormPolynomial,
    UnnormPolynomialTerm,
    UnnormMulExpr,
    UnnormFunctionCall,
};

use num_bigint::BigInt;


use std::collections::{
    btree_map::{BTreeMap, Entry as MapEntry},
    btree_set::BTreeSet,
};
use std::rc::Rc;

#[cfg(test)]
mod normal_tests;


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Polynomial {
    pub(crate) terms: BTreeMap<BTreeMap<VarOrFunc, Power>, Coefficient>,
}

type Coefficient = BigInt;
type Power = BigInt;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum VarOrFunc {
    Variable(Rc<str>),
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


pub(crate) fn normalize_polynomial(upoly: UnnormPolynomial) -> Polynomial {
    let mut poly = Polynomial {
        terms: BTreeMap::new(),
    };

    for term in upoly.terms {
        normalize_term(term, &mut poly);
    }

    // removing polynomial terms of zero coefficient.
    {
        let mut zeroed_out = BTreeSet::new();
        for (k, coeff) in poly.terms.iter() {
            if *coeff == BigInt::ZERO {
                zeroed_out.insert(k.clone());
            }
        }

        for removed in zeroed_out {
            poly.terms.remove(&removed);
        }
    }

    poly
}



fn insert_term(poly: &mut Polynomial, vars: BTreeMap<VarOrFunc, Power>, coeff: Coefficient) {
    match poly.terms.entry(vars) {
        MapEntry::Vacant(en) => _ = en.insert(coeff),
        MapEntry::Occupied(en) => *en.into_mut() += coeff,
    }
}


// normalizes one polynomial term, outputting its expanded polynomials to `out`
fn normalize_term(upoly: UnnormPolynomialTerm, out: &mut Polynomial) {
    let mut coefficient = BigInt::from(1);
    let mut var_fns = BTreeMap::<VarOrFunc, Power>::new();
    let mut norm_sub = Vec::<Polynomial>::new();

    unexpanded_normalize_term(&mut coefficient, &mut var_fns, &mut norm_sub, upoly);

    println!("{norm_sub:?}");

    let mut accum_poly = Polynomial {
        terms: BTreeMap::from([(var_fns, coefficient)]),
    };

    for subpoly in norm_sub.into_iter() {
        let mut new_accum_poly = Polynomial { terms: BTreeMap::new() };   

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
    var_fns: &mut BTreeMap<VarOrFunc, Power>,
    norm_sub: &mut Vec<Polynomial>,
    upoly: UnnormPolynomialTerm, 
) {
    for sube in upoly.mul_exprs {
        match sube {
            UnnormMulExpr::Constant(mulled_over) => {
                *coefficient *= mulled_over;
            }
            UnnormMulExpr::Variable(var) => {
                match var_fns.entry(VarOrFunc::Variable(var.into())) {
                    MapEntry::Vacant(en) => _ = en.insert(1.into()),
                    MapEntry::Occupied(en) => *en.into_mut() += 1,
                }
            }
            UnnormMulExpr::FunctionCall(func) => {
                let mut numer_out = Polynomial {
                    terms: BTreeMap::new(),
                };
                let mut denom_out = Polynomial {
                    terms: BTreeMap::new(),
                };
                let key = match func {
                    UnnormFunctionCall::Rem(numer, denom) => {
                        normalize_term(numer, &mut numer_out);
                        normalize_term(denom, &mut denom_out);

                        FunctionCall::Rem(Rc::new(numer_out), Rc::new(denom_out))
                    }
                    UnnormFunctionCall::Div(numer, denom) => {
                        normalize_term(numer, &mut numer_out);
                        normalize_term(denom, &mut denom_out);

                        FunctionCall::Div(Rc::new(numer_out), Rc::new(denom_out))
                    }
                    UnnormFunctionCall::Other { name, args } => {
                        FunctionCall::Other {
                            name: name.into(),
                            args: args.into_iter().map(normalize_polynomial).collect(),
                        }
                    }
                };

                match var_fns.entry(VarOrFunc::FunctionCall(key)) {
                    MapEntry::Vacant(en) => _ = en.insert(1.into()),
                    MapEntry::Occupied(en) => *en.into_mut() += 1,
                }
            }
            UnnormMulExpr::Parenthesis(paren) => {
                norm_sub.push(normalize_polynomial(paren))
            }
        }
    }
}













use super::{
    Polynomial,
    Varlike,
    FunctionCall as FC,
};

use num_bigint::BigInt;

use std::collections::HashMap;

#[derive(Debug)]
pub(super) enum InterpreterError {
    ZeroDenom,
    UnknownVariable(String),
}

#[derive(Debug)]
#[expect(dead_code)]
pub(super) struct UnknownVariable(String);


pub(super) fn interpret_poly(
    poly: &Polynomial, 
    vars: &HashMap<String, BigInt>
) -> Result<Option<BigInt>, UnknownVariable> {
    match interpret_poly_inner(poly, vars) {
        Ok(poly) => Ok(Some(poly)),
        Err(InterpreterError::ZeroDenom) => Ok(None),
        Err(InterpreterError::UnknownVariable(uv)) => Err(UnknownVariable(uv)),
    }
}

fn interpret_poly_inner(
    poly: &Polynomial, 
    vars: &HashMap<String, BigInt>
) -> Result<BigInt, InterpreterError> {
    let mut poly_val = BigInt::ZERO;

    for (poly_vars, coeff) in &poly.terms {
        let mut term_val: BigInt = (*coeff).into();

        for varlike in poly_vars
            .vars()
            .iter()
            .flat_map(|(varlike, power)| {
                let power = usize::try_from(power.get()).unwrap();
                std::iter::repeat_n(varlike, power)
            }) 
        { 

            let var_val = match varlike {
                Varlike::Variable(var) => {
                    let var: &str = var;

                    vars.get(var)
                    .ok_or_else(|| InterpreterError::UnknownVariable(var.into()))?
                    .clone()
                }
                Varlike::UnevaledExpr(expr) => {
                    BigInt::from_bytes_le(num_bigint::Sign::Plus, expr.as_str().as_bytes())
                }
                Varlike::FunctionCall(FC::Rem(numer, denom)) => {
                    let denom_val = interpret_poly_inner(denom, vars)?;
                    if denom_val == BigInt::ZERO {
                        return Err(InterpreterError::ZeroDenom)
                    }

                    interpret_poly_inner(numer, vars)? % denom_val
                }
                Varlike::FunctionCall(FC::Div(numer, denom)) => {
                    interpret_poly_inner(numer, vars)?
                        .checked_div(&interpret_poly_inner(denom, vars)?)
                        .ok_or_else(|| InterpreterError::ZeroDenom)?
                }
                // an arbitrary function `foo(bar, baz)` is treated as though foo is
                // `(foo * (bar + baz))`
                Varlike::FunctionCall(FC::Other {name, args}) => {
                    let name: &str = name;

                    let func_val = vars.get(name)
                        .ok_or_else(|| InterpreterError::UnknownVariable(name.into()))?
                        .clone();

                    let mut args_val = BigInt::from(args.is_empty() as isize);
                    for arg in &args[..] {
                        args_val += interpret_poly_inner(arg, vars)?;
                    }

                    func_val * args_val
                },
            };

            term_val *= var_val;
        }

        poly_val += term_val;
    }

    Ok(poly_val)
}





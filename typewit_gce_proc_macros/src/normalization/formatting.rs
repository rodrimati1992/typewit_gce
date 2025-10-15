use super::{Coefficient, FunctionCall, Polynomial, Varlike, Vars};

use std::fmt::{self, Display};



impl Display for Polynomial {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut iter = self.terms.iter();

        let Some((vars1, coeff1)) = iter.next() else {
            return write!(f, "0")
        };

        if coeff1.is_negative() {
            f.write_str("- ")?;
        }
        fmt_term(vars1, coeff1, f)?;
        
        for (vars, coeff) in iter {
            f.write_str(if coeff.is_negative() {
                " - "
            } else {
                " + "
            })?;
            fmt_term(vars, coeff, f)?;
        }

        Ok(())
    }
}

fn fmt_term(vars: &Vars, coeff: &Coefficient, f: &mut fmt::Formatter) -> fmt::Result {
    let abs_coeff = coeff.mag_prim();
    let mut print_mul = abs_coeff != 1 || vars.is_empty();
    if print_mul {
        write!(f, "{abs_coeff}")?;
    }

    for (varlike, power) in vars {
        let powered = power.get() > 1;

        if std::mem::replace(&mut print_mul, true) {
            write!(f, " * ")?;
        }
        match &varlike {
            Varlike::Variable(var) => {
                write!(f, "{var}")?;
            }
            Varlike::UnevaledExpr(expr) => {
                write!(f, "{{ {} }}", expr.as_str())?;
            }
            Varlike::FunctionCall(FunctionCall::Rem(numer, denom)) => {
                write_divlike(powered, f, " % ", numer, denom)?;
            }
            Varlike::FunctionCall(FunctionCall::Div(numer, denom)) => {
                write_divlike(powered, f, " / ", numer, denom)?;
            }
            // an arbitrary function `foo(bar, baz)` is treated as though foo it is
            // `(foo * (bar + baz))`
            Varlike::FunctionCall(FunctionCall::Other {name, args}) => {
                write!(f, "{name}(")?;
                
                let mut iter = args.iter();

                if let Some(arg) = iter.next() {
                    write!(f, "{arg}")?;
                }

                for arg in iter {
                    write!(f, ", {arg}")?;
                }
                write!(f, ")")?;
            },
        }

        if powered {
            write!(f, "**{power}")?;
        }
    }

    Ok(())
}

fn write_divlike(
    parenth_cond: bool, 
    f: &mut fmt::Formatter,
    op: &str,
    numer: &Polynomial,
    denom: &Polynomial,
) -> fmt::Result {
    parenthesized_if(parenth_cond, f, &mut |f| {
        let numer_parenth = !super::polynomial_is_unparenth_numer(numer);
        parenthesized_if(numer_parenth, f, &mut |f| Display::fmt(numer, f))?;

        f.write_str(op)?;

        let denom_parenth = !super::polynomial_is_unparenth_denom(denom);
        parenthesized_if(denom_parenth, f, &mut |f| Display::fmt(denom, f))?;

        Ok(())
    })
}


fn parenthesized_if(
    cond: bool, 
    f: &mut fmt::Formatter, 
    block: &mut dyn FnMut(&mut fmt::Formatter) -> fmt::Result,
) -> fmt::Result {
    if cond { 
        f.write_str("(")?;
    }

    block(f)?;

    if cond { 
        f.write_str(")")?;
    }

    Ok(())
}






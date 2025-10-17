#![allow(dead_code)]

use crate::i129::{I129, Sign};

use std::{
    cmp::{PartialEq, PartialOrd, Eq, Ord, Ordering},
    convert::TryFrom,
    fmt::{self, Debug, Display},
    num::{NonZeroI128, NonZeroU128},
};

use num_integer::Integer;


pub(crate) use self::nonzerobigint::NonZeroI129;

mod nonzerobigint {
    use super::*;

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub(crate) struct NonZeroI129 {
        is_negative: bool,
        magnitude: NonZeroU128,
    }

    impl NonZeroI129 {
        pub(crate) fn new(sign: Sign, magnitude: NonZeroU128) -> Self {
            Self {
                is_negative: matches!(sign, Sign::Neg),
                magnitude,
            }
        }

        pub(crate) fn is_negative(self) -> bool {
            self.is_negative
        }

        pub(crate) fn is_positive(self) -> bool {
            !self.is_negative
        }

        pub(crate) fn with_sign(mut self, sign: Sign) -> Self {
            self.is_negative = matches!(sign, Sign::Neg);
            self
        }

        pub(crate) fn sign(self) -> Sign {
            if self.is_negative {
                Sign::Neg
            } else {
                Sign::Pos
            }
        }
        
        pub(crate) fn magnitude(self) -> NonZeroU128 {
            self.magnitude
        }

        pub(crate) fn mag_prim(self) -> u128 {
            self.magnitude.get()
        }
    }

    impl NonZeroI129 {
        pub(crate) fn try_add(self, rhs: Self) -> Result<Self, IntErr> {
            fn overflowing_sub_(lhs: u128, rhs: u128) -> (u128, bool) {
                let (mag, overflow) = lhs.overflowing_sub(rhs);

                if overflow {
                    // emulating twos-complement unary `-` for u128
                    ((!mag).wrapping_add(1), overflow)
                } else {
                    (mag, overflow)
                }
            }

            let (mag, overflow) = match (self.is_negative, rhs.is_negative) { 
                (true, true) => self.mag_prim().overflowing_add(rhs.mag_prim()),
                (true, false) => overflowing_sub_(rhs.mag_prim(), self.mag_prim()),
                (false, true) => overflowing_sub_(self.mag_prim(), rhs.mag_prim()),
                (false, false) => self.mag_prim().overflowing_add(rhs.mag_prim()),
            };

            if overflow && self.is_negative == rhs.is_negative {
                Err(IntErr::Overflow(OverflowErr::new(self, &"+", rhs)))
            } else if let Some(mag) = NonZeroU128::new(mag) {
                Ok(Self {
                    is_negative: if self.is_negative == rhs.is_negative {
                        self.is_negative
                    } else {
                        overflow
                    },
                    magnitude: mag,
                })
            } else {                
                Err(IntErr::IsZero)
            }
        }

        pub(crate) fn try_mul(self, rhs: Self) -> Result<Self, OverflowErr> {
            if let Some(mag) = self.magnitude.checked_mul(rhs.magnitude) {
                Ok(Self {
                    is_negative: self.is_negative ^ rhs.is_negative,
                    magnitude: mag,
                })
            } else {                
                Err(OverflowErr::new(self, &"*", rhs))
            }
        }

        pub(crate) fn try_div(self, rhs: Self) -> Result<Self, IsZeroErr> {
            if let Some(mag) = NonZeroU128::new(self.magnitude.get() / rhs.magnitude) {
                Ok(Self {
                    is_negative: self.is_negative ^ rhs.is_negative,
                    magnitude: mag,
                })
            } else {                
                Err(IsZeroErr)
            }
        }
 
        pub(crate) fn try_rem(self, rhs: Self) -> Result<Self, IsZeroErr> {
            if let Some(mag) = NonZeroU128::new(self.magnitude.get() % rhs.magnitude) {
                Ok(Self {
                    is_negative: self.is_negative,
                    magnitude: mag,
                })
            } else {                
                Err(IsZeroErr)
            }
        }
    }
}

impl NonZeroI129 {
    pub(crate) fn abs(self) -> Self {
        Self::new(Sign::Pos, self.magnitude())
    }

    pub(crate) fn one() -> Self {
        Self::try_from(1).unwrap()
    }

    pub(crate) fn is_multiple_of(self, other: Self) -> bool {
        self.mag_prim().is_multiple_of(other.mag_prim())
    }

    pub(crate) fn gcd(self, other: Self) -> Self {
        Self::from(
            NonZeroU128::new(self.mag_prim().gcd(&other.mag_prim()))
                .expect("gcd returns a non-zero value <= min(self, other)")
        )
    }
}

impl TryFrom<i128> for NonZeroI129 {
    type Error = IntErr;

    fn try_from(n: i128) -> Result<Self, IntErr> {
        match NonZeroI128::try_from(n) {
            Ok(x) => Ok(x.into()),
            Err(_) => Err(IntErr::IsZero),
        }
    }
}

impl TryFrom<I129> for NonZeroI129 {
    type Error = IsZeroErr;

    fn try_from(n: I129) -> Result<Self, IsZeroErr> {
        match NonZeroU128::new(n.magnitude) {
            Some(nz) => Ok(Self::new(n.sign, nz)),
            None => Err(IsZeroErr),
        }
    }
}

impl From<NonZeroI128> for NonZeroI129 {
    fn from(n: NonZeroI128) -> Self {
        let sign = if n.is_negative() { Sign::Neg } else { Sign::Pos };
        Self::new(sign, n.unsigned_abs())
    }
}

impl From<Sign> for NonZeroI129 {
    fn from(sign: Sign) -> Self {
        Self::new(sign, NonZeroU128::new(1).unwrap())
    }
}

impl From<NonZeroU128> for NonZeroI129 {
    fn from(n: NonZeroU128) -> Self {
        Self::new(Sign::Pos, n)
    }
}

#[cfg(test)]
impl From<NonZeroI129> for num_bigint::BigInt {
    fn from(n: NonZeroI129) -> num_bigint::BigInt {
        num_bigint::BigInt::from_biguint(
            if n.is_negative() {
                num_bigint::Sign::Minus
            } else {
                num_bigint::Sign::Plus
            }, 
            n.mag_prim().into(),
        )
    }
}

impl PartialEq<i128> for NonZeroI129 {
    fn eq(&self, rhs: &i128) -> bool {
        match NonZeroI129::try_from(*rhs) {
            Ok(rhs) => *self == rhs,
            Err(_) => false,
        }
    }
}

impl PartialOrd<i128> for NonZeroI129 {
    fn partial_cmp(&self, rhs: &i128) -> Option<Ordering> {
        match NonZeroI129::try_from(*rhs) {
            Ok(rhs) => self.partial_cmp(&rhs),
            Err(_) if self.is_negative() => Some(Ordering::Less),
            Err(_) => Some(Ordering::Greater),
        }
    }
}

impl Debug for NonZeroI129 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_negative() {
            f.write_str("-")?;
        }
        write!(f, "{}", self.magnitude())
    }
}

impl Display for NonZeroI129 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self, f)
    }
}

////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IsZeroErr;

impl Display for IsZeroErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("attempted to store zero as non-zero type")
    }
}

impl core::error::Error for IsZeroErr {}


pub(crate) trait IsZeroOk {
    fn is_zero_ok(self) -> Option<NonZeroI129>;
}

impl IsZeroOk for Result<NonZeroI129, IsZeroErr> {
    fn is_zero_ok(self) -> Option<NonZeroI129> {
        self.ok()
    }
}


////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OverflowErr {
    lhs: NonZeroI129,
    op: &'static &'static str,
    rhs: NonZeroI129,
}

impl OverflowErr {
    pub(crate) fn new(lhs: NonZeroI129, op: &'static &'static str, rhs: NonZeroI129) -> Self {
        Self { lhs, op, rhs }
    }
}

impl Display for OverflowErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "overflow while computing `{} {} {}`",
            self.lhs,
            self.op,
            self.rhs,
        )
    }
}

impl core::error::Error for OverflowErr {}

////////////////////////////////////////////////////////////////////

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IntErr {
    Overflow(OverflowErr),
    IsZero,
}

impl From<OverflowErr> for IntErr {
    fn from(x: OverflowErr) -> Self {
        Self::Overflow(x)
    }
}

impl From<IsZeroErr> for IntErr {
    fn from(_: IsZeroErr) -> Self {
        Self::IsZero
    }
}

impl Display for IntErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow(x) => Display::fmt(x, f),
            Self::IsZero => Display::fmt(&IsZeroErr, f),
        }
    }
}

impl core::error::Error for IntErr {}

////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use crate::i129::Sign;

    use super::{IntErr, IsZeroErr, OverflowErr, NonZeroI129};

    use std::num::NonZeroU128;


    fn new_neg(n: u128) -> NonZeroI129 {
        NonZeroI129::new(Sign::Neg, n.try_into().unwrap())
    }
    fn new_pos(n: u128) -> NonZeroI129 {
        NonZeroI129::new(Sign::Pos, n.try_into().unwrap())
    }
    fn new(sign: Sign, n: u128) -> NonZeroI129 {
        NonZeroI129::new(sign, n.try_into().unwrap())
    }
    fn from_lit(n: i128) -> NonZeroI129 {
        n.try_into().unwrap()
    }


    #[test]
    fn test_is_pos_neg() {
        {
            let pos = NonZeroI129::try_from(3i128).unwrap();
            assert!(pos.is_positive());
            assert!(!pos.is_negative());
        }
        {
            let neg = NonZeroI129::try_from(-3i128).unwrap();
            assert!(!neg.is_positive());
            assert!(neg.is_negative());
        }
    }

    #[test]
    fn test_sign() {
        {
            let pos = NonZeroI129::new(Sign::Pos, 1u128.try_into().unwrap());
            assert_eq!(pos.sign(), Sign::Pos);
            assert_eq!(pos.with_sign(Sign::Neg).sign(), Sign::Neg);
        }
        {
            let neg = NonZeroI129::new(Sign::Neg, 1u128.try_into().unwrap());
            assert_eq!(neg.sign(), Sign::Neg);
            assert_eq!(neg.with_sign(Sign::Pos).sign(), Sign::Pos);
        }
    }

    #[test]
    fn test_abs() {
        let pos = NonZeroI129::try_from(3i128).unwrap();
        assert_eq!(pos.abs(), pos);
        
        
        let neg = NonZeroI129::try_from(-3i128).unwrap();
        assert_eq!(neg.abs(), pos);
    }

    #[test]
    fn test_one() {
        assert_eq!(NonZeroI129::one(), NonZeroI129::try_from(1i128).unwrap());
    }

    #[test]
    fn test_magnitude() {
        let pos = NonZeroI129::try_from(3i128).unwrap();
        assert_eq!(pos.magnitude(), NonZeroU128::new(3u128).unwrap());
        assert_eq!(pos.mag_prim(), 3u128);
        
        let neg = NonZeroI129::try_from(-5i128).unwrap();
        assert_eq!(neg.magnitude(), NonZeroU128::new(5u128).unwrap());
        assert_eq!(neg.mag_prim(), 5u128);
    }

    #[test]
    fn test_multiple_of_and_gcd() {
        use num_integer::Integer;

        let range = (-12..=12i128).filter(|x| *x != 0);

        for lhs in range.clone() {
            for rhs in range.clone() {
                let gcd = NonZeroI129::try_from(lhs).unwrap()
                    .gcd(NonZeroI129::try_from(rhs).unwrap());

                let is_multiple_of = NonZeroI129::try_from(lhs).unwrap()
                    .is_multiple_of(NonZeroI129::try_from(rhs).unwrap());

                assert_eq!(gcd, NonZeroI129::try_from(lhs.gcd(&rhs)).unwrap());
                assert_eq!(is_multiple_of, lhs.is_multiple_of(&rhs));
            } 
        }
    }

    #[test]
    fn test_add_small() {
        let iter = (-10..=10).filter(|x| *x != 0);
        for lhs in iter.clone() {
            for rhs in iter.clone() {
                if lhs == -rhs {
                    assert_eq!(
                        from_lit(lhs).try_add(from_lit(rhs)).unwrap_err(), 
                        IntErr::IsZero,
                    );
                } else {
                    assert_eq!(
                        from_lit(lhs).try_add(from_lit(rhs)).unwrap(),
                        from_lit(lhs + rhs),
                        "{lhs} + {rhs}"
                    );
                }
            }
        }
    }

    #[test]
    fn test_add_overflow() {
        for sign in [Sign::Neg, Sign::Pos] {            
            assert_eq!(
                new(sign, u128::MAX - 2).try_add(new(sign, 1)).unwrap(),
                new(sign, u128::MAX - 1),
            );
            assert_eq!(
                new(sign, u128::MAX - 2).try_add(new(sign, 2)).unwrap(),
                new(sign, u128::MAX),
            );
            assert_eq!(
                new(sign, u128::MAX - 2).try_add(new(sign, 3)).unwrap_err(),
                IntErr::Overflow(OverflowErr::new(new(sign, u128::MAX - 2), &"+", new(sign, 3))),
            );
        }
    }

    #[test]
    fn test_div_sign() {
        assert_eq!(new_pos(10).try_div(new_pos(3)).unwrap(), new_pos(3));
        assert_eq!(new_pos(10).try_div(new_neg(4)).unwrap(), new_neg(2));
        assert_eq!(new_neg(10).try_div(new_pos(3)).unwrap(), new_neg(3));
        assert_eq!(new_neg(10).try_div(new_neg(10)).unwrap(), new_pos(1));
    }
    
    #[test]
    fn test_div_err() {
        assert_eq!(new_pos(10).try_div(new_pos(10)).unwrap(), new_pos(1));

        assert_eq!(new_pos(10).try_div(new_pos(11)).unwrap_err(), IsZeroErr);
    }


    #[test]
    fn test_mul_small() {
        let iter = (-10..=10).filter(|x| *x != 0);
        for lhs in iter.clone() {
            for rhs in iter.clone() {
                assert_eq!(
                    from_lit(lhs).try_mul(from_lit(rhs)).unwrap(),
                    from_lit(lhs * rhs),
                    "{lhs} + {rhs}"
                );
            }
        }
    }
    
    #[test]
    fn test_mul_err() {
        let u64max = u128::from(u64::MAX);

        for (lhs_sign, rhs_sign, res_sign) in [
            (Sign::Pos, Sign::Pos, Sign::Pos),
            (Sign::Pos, Sign::Neg, Sign::Neg),
            (Sign::Neg, Sign::Pos, Sign::Neg),
            (Sign::Neg, Sign::Neg, Sign::Pos),
        ] {
            assert_eq!(
                new(lhs_sign, u64max).try_mul(new(rhs_sign, u64max)).unwrap(), 
                new(res_sign, u64max * u64max),
            );
            assert_eq!(
                new(lhs_sign, u64max).try_mul(new(rhs_sign, u64max + 1)).unwrap(), 
                new(res_sign, u64max * (u64max + 1)),
            );
            assert_eq!(
                new(lhs_sign, u64max + 1).try_mul(new(rhs_sign, u64max)).unwrap(), 
                new(res_sign, (u64max + 1) * u64max),
            );
            assert_eq!(
                new(lhs_sign, u64max + 1).try_mul(new(rhs_sign, u64max + 1)).unwrap_err(), 
                OverflowErr::new(new(lhs_sign, u64max + 1), &"*", new(rhs_sign, u64max + 1))
            );
        }
    }
}











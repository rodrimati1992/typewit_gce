use std::{
    cmp::{PartialEq, Eq},
    fmt::{self, Debug},
};

#[derive(Copy, Clone)]
pub(crate) struct I129 {
    pub sign: Sign,
    pub magnitude: u128,
}


impl I129 {
    pub(crate) fn from_str_radix(s: &str, radix: u32) -> Result<Self, std::num::ParseIntError> {
        i128::from_str_radix(s, radix)
            .map(Self::from)
            .or_else(|_| {
                u128::from_str_radix(s, radix)
                    .map(|magnitude| Self { sign: Sign::Pos , magnitude })
            })
    }
}

impl From<i128> for I129 {
    fn from(n: i128) -> Self {
        Self{
            sign: if n < 0 { Sign::Neg } else { Sign::Pos },
            magnitude: n.unsigned_abs(),
        }
    }
}

impl Debug for I129 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.sign == Sign::Neg {
            f.write_str("-")?;
        }
        write!(f, "{}", self.magnitude)
    }
}

impl fmt::Display for I129 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self, f)
    }
}


impl PartialEq for I129 {
    fn eq(&self, rhs: &Self) -> bool {
        self.magnitude == 0 && rhs.magnitude == 0
        || (self.sign == rhs.sign && self.magnitude == rhs.magnitude)
    }
}
impl Eq for I129 {}

////////////////////////////////////////

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Sign {
    Neg = -1,
    Pos = 1,
}

impl std::ops::Neg for Sign {
    type Output = Self;
    
    fn neg(self) -> Self {
        match self {
            Sign::Neg => Sign::Pos,
            Sign::Pos => Sign::Neg,
        }
    }
}

impl std::ops::Mul for Sign {
    type Output = Self;
    
    fn mul(self, rhs: Sign) -> Self {
        match self {
            Sign::Neg => -rhs,
            Sign::Pos => rhs,
        }
    }
}

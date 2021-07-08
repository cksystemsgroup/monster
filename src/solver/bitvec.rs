use std::{
    fmt,
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Not, Rem, Shl, Shr, Sub},
};

#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd)]
pub struct BitVector(pub u64);

impl BitVector {
    pub fn ones() -> BitVector {
        BitVector(u64::max_value())
    }

    pub fn ctz(&self) -> u32 {
        self.0.trailing_zeros()
    }

    pub fn cno(&self) -> u32 {
        self.0.count_ones()
    }

    pub fn odd(&self) -> bool {
        self.0 % 2 == 1
    }

    pub fn lsb(&self) -> u64 {
        self.0 & 1
    }

    pub fn modinverse(&self) -> Option<BitVector> {
        modinverse::modinverse((self.0 as u128) as i128, 2_i128.pow(64))
            .map(|res| BitVector(res as u64))
    }

    pub fn addo(&self, t: BitVector) -> bool {
        self.0.overflowing_add(t.0).1
    }

    pub fn mulo(&self, t: BitVector) -> bool {
        self.0.overflowing_mul(t.0).1
    }

    pub fn bit(&self, n: u32) -> BitVector {
        BitVector((self.0 >> n) & 1)
    }

    pub fn mask(n: u64) -> BitVector {
        if let Some(b) = u64::max_value().checked_shl((64 - n) as u32) {
            BitVector(b)
        } else {
            BitVector(0)
        }
    }
}

impl Neg for BitVector {
    type Output = BitVector;

    fn neg(self) -> Self::Output {
        Self(-(self.0 as i64) as u64)
    }
}

impl Add<BitVector> for BitVector {
    type Output = BitVector;

    fn add(self, other: BitVector) -> Self::Output {
        Self(self.0.wrapping_add(other.0))
    }
}

impl Sub<BitVector> for BitVector {
    type Output = BitVector;

    fn sub(self, other: BitVector) -> Self::Output {
        Self(self.0.wrapping_sub(other.0))
    }
}

impl Mul<BitVector> for BitVector {
    type Output = BitVector;

    fn mul(self, other: BitVector) -> Self::Output {
        Self(self.0.wrapping_mul(other.0))
    }
}

impl Div<BitVector> for BitVector {
    type Output = BitVector;

    fn div(self, other: BitVector) -> Self::Output {
        if other == BitVector(0) {
            Self::ones()
        } else {
            Self(self.0.wrapping_div(other.0))
        }
    }
}

impl Rem<BitVector> for BitVector {
    type Output = BitVector;

    fn rem(self, other: BitVector) -> Self::Output {
        if other == BitVector(0) {
            self
        } else {
            Self(self.0.wrapping_rem(other.0))
        }
    }
}

impl BitOr<BitVector> for BitVector {
    type Output = BitVector;

    fn bitor(self, other: BitVector) -> Self::Output {
        Self(self.0 | other.0)
    }
}

impl BitAnd<BitVector> for BitVector {
    type Output = BitVector;

    fn bitand(self, other: BitVector) -> Self::Output {
        Self(self.0 & other.0)
    }
}

impl BitXor<BitVector> for BitVector {
    type Output = BitVector;

    fn bitxor(self, other: BitVector) -> Self::Output {
        Self(self.0 ^ other.0)
    }
}

impl Shl<u32> for BitVector {
    type Output = BitVector;

    fn shl(self, other: u32) -> Self::Output {
        Self(self.0.wrapping_shl(other))
    }
}

impl Shr<u32> for BitVector {
    type Output = BitVector;

    fn shr(self, other: u32) -> Self::Output {
        Self(self.0.wrapping_shr(other))
    }
}

impl Not for BitVector {
    type Output = BitVector;

    fn not(self) -> Self::Output {
        BitVector(!self.0)
    }
}

impl fmt::Debug for BitVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn bit_to_char(x: &BitVector, b: u32) -> char {
            if *x & (BitVector(1) << b) > BitVector(0) {
                '1'
            } else {
                '0'
            }
        }

        let bit_vector = (0..64)
            .rev()
            .map(|b| bit_to_char(self, b))
            .skip_while(|c| *c == '0')
            .collect::<String>();

        write!(f, "<{}>", bit_vector)
    }
}

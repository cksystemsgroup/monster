#![allow(clippy::many_single_char_names)]
#![allow(clippy::suspicious_operation_groupings)]
#![allow(clippy::too_many_arguments)]

use super::BitVector;
use rand::{distributions::Uniform, seq::SliceRandom, thread_rng, Rng};
use std::fmt;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TError {
    #[error("inconsistency detected, constraint not satisfiable")]
    Invalid,
}

pub type CPResult<T> = Result<T, TError>;

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub struct TritVector {
    pub l: BitVector,
    pub u: BitVector,
}

impl Default for TritVector {
    fn default() -> Self {
        Self {
            l: BitVector(0),
            u: BitVector::ones(),
        }
    }
}

impl TritVector {
    pub fn new(l: u64, u: u64) -> Result<Self, TError> {
        Self {
            l: BitVector(l),
            u: BitVector(u),
        }
        .validate()
    }

    pub fn zero() -> Self {
        Self {
            l: BitVector(0),
            u: BitVector(0),
        }
    }

    pub fn one() -> Self {
        Self {
            l: BitVector(1),
            u: BitVector(1),
        }
    }

    pub fn ones() -> Self {
        Self {
            l: BitVector::ones(),
            u: BitVector::ones(),
        }
    }

    pub fn fixed(&self) -> bool {
        self.l == self.u
    }

    fn bit(&self, n: u32) -> Self {
        Self {
            l: self.l.bit(n),
            u: self.u.bit(n),
        }
    }

    fn sign_extend_bit(&self, n: u32) -> Self {
        let b = Self {
            l: self.l.bit(n),
            u: self.u.bit(n),
        };
        match b {
            one if one == TritVector::one() => TritVector::ones(),
            zero if zero == TritVector::zero() => zero,
            _ => Self {
                l: BitVector(0),
                u: BitVector::ones(),
            },
        }
    }

    fn validate(self) -> Result<Self, TError> {
        if (!self.l | self.u) != BitVector::ones() {
            return Err(TError::Invalid);
        }

        Ok(self)
    }

    pub fn find_next_higher_match(&self, b: BitVector) -> (BitVector, bool) {
        let set = self.l | b & self.u;
        let set2cl = b & !set;
        let cl2set = !b & set;

        if cl2set == set2cl {
            (b, false)
        } else if cl2set > set2cl {
            // next higher value with bit i set has bits [i-1...0] cleared
            let size = 64 - cl2set.clz() - 1;
            let mask0 = BitVector::ones() << size;
            let can_cl = mask0 | self.l;

            if set & can_cl >= b {
                (set & can_cl, false)
            } else {
                (set & can_cl, true)
            }
        } else {
            // next higher value with bit i cleared has next clear bit {i+1...64} set.
            let size = 64 - set2cl.clz() - 1;
            let cl_can_set = !set & self.u;
            let left_cl_can_set = (cl_can_set >> size) << size;
            let next_to_set = left_cl_can_set.ctz();
            // takes care of next_to_set = 64, next_to_set is never 0
            let set = set | BitVector(1) << (next_to_set - 1) << 1;
            let mask0 = BitVector::ones() << (next_to_set - 1) << 1;
            let can_cl = mask0 | self.l;

            if set & can_cl >= b {
                (set & can_cl, false)
            } else {
                (set & can_cl, true)
            }
        }
    }

    pub fn find_next_lower_match(&self, b: BitVector) -> (BitVector, bool) {
        let set = self.l | b & self.u;
        let set2cl = b & !set;
        let cl2set = !b & set;

        if set2cl == cl2set {
            (b, false)
        } else if set2cl > cl2set {
            // next lower value with bit i cleared has bits [i-1...0] set
            let size = set2cl.clz() + 1;
            let mask1 = BitVector::ones() >> (size - 1) >> 1;
            let can_set = mask1 & self.u;

            if set | can_set <= b {
                (set | can_set, false)
            } else {
                (set | can_set, true)
            }
        } else {
            // next lower value with bit i set has next set bit {i+1...64} cleared.
            let size = 64 - cl2set.clz() - 1;
            let set_can_clear = set & !self.l;
            let left_set_can_clear = (set_can_clear >> size) << size;
            let next_to_clear = left_set_can_clear.ctz();
            // takes care of next_to_clear = 64, next_to_clear is never 0
            let set = set & !(BitVector(1) << (next_to_clear - 1) << 1);
            let mask1 = BitVector::ones() >> (64 - next_to_clear);
            let can_set = mask1 & self.u;

            if set | can_set <= b {
                (set | can_set, false)
            } else {
                (set | can_set, true)
            }
        }
    }

    pub fn random_sample_inclusive(&self, l: u64, u: u64) -> Option<BitVector> {
        let (end, wrap) = self.find_next_lower_match(BitVector(u));
        if !wrap && l <= end.0 {
            let random = thread_rng().sample(Uniform::new_inclusive(l, end.0));
            Some(self.find_next_higher_match(BitVector(random)).0)
        } else {
            None
        }
    }

    pub fn random_sample(&self, l: u64, u: u64) -> Option<BitVector> {
        let (end, wrap) = self.find_next_lower_match(BitVector(u - 1));
        if !wrap && l <= end.0 {
            let random = thread_rng().sample(Uniform::new_inclusive(l, end.0));
            Some(self.find_next_higher_match(BitVector(random)).0)
        } else {
            None
        }
    }

    pub fn mcb(&self, b: BitVector) -> bool {
        (self.u & b == b) && (self.l | b == b)
    }

    pub fn force_cbs_onto(&self, b: BitVector) -> BitVector {
        (self.l | b) & self.u
    }

    fn constrain_eq(self, y: TritVector) -> CPResult<(TritVector, TritVector)> {
        let z = Self {
            l: self.l | y.l,
            u: self.u & y.u,
        }
        .validate()?;

        Ok((z, z))
    }

    fn constrain_neg(self, y: TritVector) -> CPResult<(TritVector, TritVector)> {
        let z = Self {
            l: self.l | !y.u,
            u: self.u & !y.l,
        };

        let y = Self {
            l: y.l | !self.u,
            u: y.u & !self.l,
        };

        Ok((z.validate()?, y.validate()?))
    }

    pub fn constrain_not(self, y: TritVector) -> CPResult<(TritVector, TritVector)> {
        let z = Self {
            l: (self.l | !y.u) & BitVector(1),
            u: (self.u & !y.l) & BitVector(1),
        };

        let y = Self {
            l: (y.l | !self.u) & BitVector(1),
            u: (y.u & !self.l) & BitVector(1),
        };

        Ok((z.validate()?, y.validate()?))
    }

    fn constrain_xor(
        self,
        x: TritVector,
        y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let z = Self {
            l: self.l | (!x.u & y.l) | (x.l & !y.u),
            u: self.u & (x.u | y.u) & (!(x.l & y.l)),
        };

        let x = Self {
            l: x.l | (!self.u & y.l) | self.l & !y.u,
            u: x.u & (self.u | y.u) & (!(y.l & self.l)),
        };

        let y = Self {
            l: y.l | (!self.u & x.l) | (self.l & !x.u),
            u: y.u & (self.u | x.u) & (!(x.l & self.l)),
        };

        Ok((z.validate()?, x.validate()?, y.validate()?))
    }

    pub fn constrain_and(
        self,
        x: TritVector,
        y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let z = Self {
            l: self.l | (x.l & y.l),
            u: self.u & x.u & y.u,
        };
        let x = Self {
            l: x.l | self.l,
            u: x.u & !((!self.u) & y.l),
        };
        let y = Self {
            l: y.l | self.l,
            u: y.u & !((!self.u) & x.l),
        };

        Ok((z.validate()?, x.validate()?, y.validate()?))
    }

    fn constrain_or(
        self,
        x: TritVector,
        y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let z = Self {
            l: self.l | x.l | y.l,
            u: self.u & (x.u | y.u),
        };
        let x = Self {
            l: x.l | ((!y.u) & self.l),
            u: x.u & self.u,
        };
        let y = Self {
            l: y.l | ((!x.u) & self.l),
            u: y.u & self.u,
        };

        Ok((z.validate()?, x.validate()?, y.validate()?))
    }

    fn constrain_shl(
        self,
        x: TritVector,
        y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let mask1 = BitVector::mask(y.u.0);
        let mask2 = BitVector::mask(64 - y.u.0);

        let z = Self {
            l: ((x.l << (y.u.0) as u32) | self.l) & mask2,
            u: (x.u << (y.u.0) as u32) & self.u,
        };
        let x = Self {
            l: x.l | (self.l >> (y.u.0) as u32),
            u: ((self.u >> (y.u.0) as u32) | mask1) & x.u,
        };

        Ok((z.validate()?, x.validate()?, y.validate()?))
    }

    fn constrain_ite(
        self,
        b: TritVector,
        x: TritVector,
        y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector, TritVector)> {
        let mut b = Self {
            l: b.l | (self.l & !y.u) | (!self.u & y.l),
            u: b.u & (!self.l | x.u) & (self.u | !x.l),
        };

        let t = b.l | !b.u;
        if t != BitVector(0) {
            if t & b.l == BitVector(0) {
                b = TritVector::zero();
            } else {
                b = TritVector::ones();
            }
        }

        let z = Self {
            l: self.l | (b.l & x.l) | (!b.u & y.l) | (x.l & y.l),
            u: self.u & (!b.l | x.u) & (b.u | y.u) & (x.u | y.u),
        };
        let x = Self {
            l: x.l | (self.l & (b.l | !y.u)),
            u: x.u & !(!self.u & (b.l | y.l)),
        };
        let y = Self {
            l: y.l | (self.l & (!b.u | !x.u)),
            u: y.u & (self.u | (b.u & !x.l)),
        };

        Ok((z.validate()?, b.validate()?, x.validate()?, y.validate()?))
    }

    pub fn constrain_add(
        self,
        mut x: TritVector,
        mut y: TritVector,
        o: bool,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        // TODO: check for cases that the fulladder cannot infer and add constraints if necessary,
        //       like xor = x ^ and | y ^ and
        fn shuffled_fulladder(
            mut z: TritVector,
            add: [TritVector; 3],
            mut co: TritVector,
        ) -> CPResult<(TritVector, TritVector, TritVector, TritVector, TritVector)> {
            let mut s = vec![0, 1, 2];
            s.shuffle(&mut thread_rng());

            let (mut x, mut y, mut c) = (add[s[0]], add[s[1]], add[s[2]]);
            let mut t = [TritVector::default(); 5];

            loop {
                // z = (x ^ y) ^ c
                let (t_0, nx, ny) = t[0].constrain_xor(x, y)?;
                let (nz, t_0, nc) = z.constrain_xor(t_0, c)?;

                // co = x & y | c & (x | y) or x & y | x & c | y & c
                let (t_1, nx, ny) = t[1].constrain_and(nx, ny)?;
                let (t_2, nx, ny) = t[2].constrain_or(nx, ny)?;
                let (t_3, nc, t_2) = t[3].constrain_and(nc, t_2)?;
                let (nco, t_1, t_3) = co.constrain_or(t_1, t_3)?;

                // and = and & !xor
                let (t_4, _) = t[4].constrain_neg(t_0)?;
                let (t_1, _, t_4) = t_1.constrain_and(t_1, t_4)?;

                // z = 0, co = 0 => 000, z = 1, co = 1 => 1111
                let nx = TritVector {
                    l: nx.l | nco.l & nz.l,
                    u: nx.u & (nco.u | nz.u),
                }
                .validate()?;

                let ny = TritVector {
                    l: ny.l | nco.l & nz.l,
                    u: ny.u & (nco.u | nz.u),
                }
                .validate()?;

                let nc = TritVector {
                    l: nc.l | nco.l & nz.l,
                    u: nc.u & (nco.u | nz.u),
                }
                .validate()?;

                if (z, x, y, c, co, t) == (nz, nx, ny, nc, nco, [t_0, t_1, t_2, t_3, t_4]) {
                    let mut rev_s: Vec<_> = s.into_iter().enumerate().collect();
                    rev_s.sort_by_key(|k| k.1);

                    let rev_s: Vec<_> = rev_s.into_iter().map(|k| k.0).collect();

                    let shuffled = [x, y, c];
                    let (x, y, c) = (shuffled[rev_s[0]], shuffled[rev_s[1]], shuffled[rev_s[2]]);

                    return Ok((z, x, y, c, co));
                }

                z = nz;
                x = nx;
                y = ny;
                c = nc;
                co = nco;
                t = [t_0, t_1, t_2, t_3, t_4];
            }
        }

        let (mut co, mut c) = (TritVector::default(), TritVector::default());
        let mut z = self;

        loop {
            let (nz, nx, ny, nc, nco) = shuffled_fulladder(z, [x, y, c], co)?;

            // force msb to 0 in non-overflowing addition
            let nco = if !o {
                TritVector {
                    l: nco.l,
                    u: nco.u & !(BitVector(1) << 63),
                }
                .validate()?
            } else {
                nco
            };

            // c = co << 1
            let (nc, nco, _) = nc.constrain_shl(nco, TritVector::one())?;

            if (z, x, y, c, co) == (nz, nx, ny, nc, nco) {
                return Ok((z, x, y));
            }

            z = nz;
            x = nx;
            y = ny;
            c = nc;
            co = nco;
        }
    }

    pub fn constrain_sub(
        self,
        mut x: TritVector,
        mut y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let mut t = [TritVector::default(); 2];
        let mut z = self;

        loop {
            // z = x + (~y) + 1
            let (t_0, ny) = t[0].constrain_neg(y)?;
            let (t_1, nx, t_0) = t[1].constrain_add(x, t_0, true)?;
            let (nz, t_1, _) = z.constrain_add(t_1, TritVector::one(), true)?;

            if (x, y, z, t) == (nx, ny, nz, [t_0, t_1]) {
                return Ok((z, x, y));
            }

            z = nz;
            x = nx;
            y = ny;
            t = [t_0, t_1];
        }
    }

    fn constrain_diseq(self, y: TritVector) -> CPResult<(TritVector, TritVector)> {
        fn diseq(x: TritVector, y: TritVector) -> (TritVector, TritVector) {
            // x fixed, y possibly not fixed
            if x.fixed() && (x.l == y.l || x.l == y.u) {
                let f = y.l ^ y.u;
                //one bit unknown
                if f.cno() == 1 {
                    return (
                        x,
                        TritVector {
                            l: x.l ^ f,
                            u: x.l ^ f,
                        },
                    );
                }
            }
            (x, y)
        }

        if self.fixed() && y.fixed() && self.l == y.l {
            return Err(TError::Invalid);
        }
        if self.l & !y.u | !self.u & y.l != BitVector(0) {
            return Ok((self.validate()?, y.validate()?));
        }

        let (ny, nx) = diseq(y, self);
        let (nx, ny) = diseq(nx, ny);

        Ok((nx.validate()?, ny.validate()?))
    }

    pub fn constrain_reif_eq(
        self,
        x: TritVector,
        y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let z = self.bit(0).validate()?;
        let x = x.validate()?;
        let y = y.validate()?;

        if z.l == BitVector(1) {
            let (nx, ny) = x.constrain_eq(y)?;
            return Ok((z, nx, ny));
        } else if z.u == BitVector(0) {
            let (nx, ny) = x.constrain_diseq(y)?;
            return Ok((z, nx, ny));
        } else if x.fixed() && y.fixed() && x.l == y.l {
            return Ok((TritVector::one(), x, y));
        } else {
            let t = x.l & !y.u | !x.u & y.l;
            if t != BitVector(0) {
                return Ok((TritVector::zero(), x, y));
            }
        }
        Ok((z, x, y))
    }

    fn constrain_lt(self, y: TritVector) -> CPResult<(TritVector, TritVector)> {
        self.constrain_ineq(y, |x, y| x >= y)
    }

    fn constrain_gte(self, y: TritVector) -> CPResult<(TritVector, TritVector)> {
        let (y, x) = y.constrain_ineq(self, |x, y| x > y)?;
        Ok((x, y))
    }

    fn constrain_ineq<F>(self, mut y: TritVector, f: F) -> CPResult<(TritVector, TritVector)>
    where
        F: Fn(BitVector, BitVector) -> bool,
    {
        if f(self.l, y.u) {
            return Err(TError::Invalid);
        }
        let mut x = self;

        for i in (0..64).rev() {
            //propagate x
            if !x.bit(i).fixed() {
                let xl = x.l | (BitVector(1) << i);
                if f(xl, y.u) {
                    x = TritVector {
                        l: x.l,
                        u: x.u ^ (BitVector(1) << i),
                    }
                } else {
                    break;
                }
            }
        }

        for i in (0..64).rev() {
            //propagate y
            if !y.bit(i).fixed() {
                let yu = y.u ^ (BitVector(1) << i);
                if f(x.l, yu) {
                    y = TritVector {
                        l: y.l | (BitVector(1) << i),
                        u: y.u,
                    };
                } else {
                    break;
                }
            }
        }

        Ok((x.validate()?, y.validate()?))
    }

    pub fn constrain_reif_sltu(
        self,
        x: TritVector,
        y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let z = self.bit(0).validate()?;
        let x = x.validate()?;
        let y = y.validate()?;

        if z.l == BitVector(1) {
            let (nx, ny) = x.constrain_lt(y)?;
            return Ok((z, nx, ny));
        } else if z.u == BitVector(0) {
            let (nx, ny) = x.constrain_gte(y)?;
            return Ok((z, nx, ny));
        } else if x.fixed() && y.fixed() && x.l < y.l {
            return Ok((TritVector::one(), x, y));
        } else if z.l >= y.u {
            return Ok((TritVector::zero(), x, y));
        }
        Ok((z, x, y))
    }

    pub fn constrain_mul(
        self,
        mut x: TritVector,
        mut y: TritVector,
        o: bool,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        fn build_y(yi: &[TritVector; 64], y: TritVector) -> TritVector {
            let mask = BitVector(1);
            let mut yl = BitVector(0);
            let mut yu = BitVector(0);

            for (i, e) in yi.iter().enumerate() {
                yl = yl | (e.l & (mask << i as u32));
                yu = yu | (e.u & (mask << i as u32));
            }

            TritVector {
                l: yl,
                u: y.force_cbs_onto(yu),
            }
        }

        let mut t_shl = [TritVector::default(); 64];
        let mut t_ite = [TritVector::default(); 64];
        let mut t_add = [TritVector::default(); 64];
        let mut yi = [TritVector::default(); 64];

        let mut change = true;
        let mut prev = 0;
        t_add[63] = self;

        while change {
            change = false;
            for i in (0..64)
                .filter(|i| *i == 0 || y.bit(*i).u != BitVector(0))
                .map(|i| i as usize)
            {
                let (t_s, nx, _) =
                    t_shl[i].constrain_shl(x, TritVector::new(i as u64, i as u64)?)?;
                let (t_i, nyi, t_s, _) =
                    t_ite[i].constrain_ite(y.sign_extend_bit(i as u32), t_s, TritVector::zero())?;

                if (x, t_shl[i], t_ite[i], yi[i]) != (nx, t_s, t_i, nyi) {
                    change = true;
                    x = nx;
                    t_shl[i] = t_s;
                    t_ite[i] = t_i;
                    yi[i] = nyi;
                }
            }

            let (t_a, t_i) = t_add[0].constrain_eq(t_ite[0])?;
            if (t_add[0], t_ite[0]) != (t_a, t_i) {
                change = true;
                t_add[0] = t_a;
                t_ite[0] = t_i;
            }

            prev = 0;

            for i in (1..64)
                .filter(|i| y.bit(*i).u != BitVector(0))
                .map(|i| i as usize)
            {
                let (t_ai, t_aii, t_i) = t_add[i].constrain_add(t_add[prev], t_ite[i], o)?;

                if (t_add[i], t_add[prev], t_ite[i]) != (t_ai, t_aii, t_i) {
                    change = true;
                    t_add[i] = t_ai;
                    t_add[prev] = t_aii;
                    t_ite[i] = t_i;
                }

                prev = i;
            }

            let (t_z, _) = t_add[prev].constrain_eq(t_add[63])?;

            if t_z != t_add[prev] {
                change = true;
                t_add[prev] = t_z;
            }

            let ny = build_y(&yi, y).validate()?;

            if y != ny {
                change = true;
                y = ny;
            }
        }

        Ok((t_add[prev], x, y))
    }

    pub fn constrain_divu(
        self,
        mut x: TritVector,
        mut y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let mut t = TritVector::default();
        let mut r = TritVector::default();
        let mut z = self;

        loop {
            let (nt, ny, nz) = t.constrain_mul(y, self, false)?;
            let (nx, nt, nr) = x.constrain_add(nt, r, false)?;
            let (nr, ny) = nr.constrain_lt(ny)?;

            if (nt, nr, nx, ny, nz) == (t, r, x, y, z) {
                return Ok((z, x, y));
            }

            z = nz;
            x = nx;
            y = ny;
            t = nt;
            r = nr;
        }
    }

    pub fn constrain_remu(
        self,
        mut x: TritVector,
        mut y: TritVector,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        let mut t = TritVector::default();
        let mut q = TritVector::default();
        let mut z = self;

        loop {
            let (nt, ny, nq) = t.constrain_mul(y, q, false)?;
            let (nx, nt, nz) = x.constrain_add(nt, z, false)?;
            let (nz, ny) = nz.constrain_lt(ny)?;

            if (nt, nq, nx, ny, nz) == (t, q, x, y, z) {
                return Ok((z, x, y));
            }

            z = nz;
            x = nx;
            y = ny;
            t = nt;
            q = nq;
        }
    }
}

impl fmt::Display for TritVector {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<{:b}, {:b}>", self.l.0, self.u.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_constrain_two_ops(
        op: &str,
        xl: u64,
        xu: u64,
        yl: u64,
        yu: u64,
        rxl: u64,
        rxu: u64,
        ryl: u64,
        ryu: u64,
    ) -> CPResult<()> {
        let x = TritVector::new(xl, xu).expect("new TritVector");
        let y = TritVector::new(yl, yu).expect("new TritVector");
        let rx = TritVector::new(rxl, rxu).expect("new TritVector");
        let ry = TritVector::new(ryl, ryu).expect("new TritVector");

        if let Ok((x, y)) = match op {
            "=" => x.constrain_eq(y),
            "!" => x.constrain_neg(y),
            _ => panic!("unknown operation"),
        } {
            assert_eq!(x, rx);
            assert_eq!(y, ry);
        } else {
            return Err(TError::Invalid);
        }

        Ok(())
    }

    fn test_constrain_three_ops(
        op: &str,
        xl: u64,
        xu: u64,
        yl: u64,
        yu: u64,
        zl: u64,
        zu: u64,
        rxl: u64,
        rxu: u64,
        ryl: u64,
        ryu: u64,
        rzl: u64,
        rzu: u64,
    ) -> CPResult<()> {
        let x = TritVector::new(xl, xu).expect("new TritVector");
        let y = TritVector::new(yl, yu).expect("new TritVector");
        let z = TritVector::new(zl, zu).expect("new TritVector");
        let rx = TritVector::new(rxl, rxu).expect("new TritVector");
        let ry = TritVector::new(ryl, ryu).expect("new TritVector");
        let rz = TritVector::new(rzl, rzu).expect("new TritVector");

        if let Ok((z, x, y)) = match op {
            "&" => z.constrain_and(x, y),
            "|" => z.constrain_or(x, y),
            "^" => z.constrain_xor(x, y),
            "<<" => z.constrain_shl(x, y),
            "+" => z.constrain_add(x, y, true),
            "-" => z.constrain_sub(x, y),
            "*" => z.constrain_mul(x, y, true),
            "/" => z.constrain_divu(x, y),
            "%" => z.constrain_remu(x, y),
            "==" => z.constrain_reif_eq(x, y),
            "<" => z.constrain_reif_sltu(x, y),
            "ite" => {
                if let Ok((z, _b, x, y)) = z.constrain_ite(TritVector::default(), x, y) {
                    Ok((z, x, y))
                } else {
                    Err(TError::Invalid)
                }
            }
            _ => panic!("unknown operation"),
        } {
            assert_eq!(x, rx);
            assert_eq!(y, ry);
            assert_eq!(z, rz);
        } else {
            panic!("unsat constraint")
        }

        Ok(())
    }

    #[test]
    fn test_bitwise_constrain_ops() {
        let mut res = test_constrain_two_ops(
            "=", 0b1000, 0b1101, 0b0100, 0b1101, 0b1100, 0b1101, 0b1100, 0b1101,
        );
        assert_eq!(res.is_ok(), true);

        res = test_constrain_two_ops(
            "=", 0b1000, 0b1101, 0b0100, 0b1101, 0b1100, 0b1101, 0b1100, 0b1101,
        );
        assert_eq!(res.is_ok(), true);

        res = test_constrain_two_ops(
            "!", 0b1000, 0b1101, !0b1101, !0b0100, 0b1100, 0b1101, !0b1101, !0b1100,
        );
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "^", 0b1000, 0b1101, //<0..0 1*0*>
            0b0100, 0b1101, //<0..0 *10*>
            0b1001, 0b1011, //<0..0 10*1>
            0b1100, 0b1101, //<0..0 110*>
            0b0100, 0b0101, //<0..0 010*>
            0b1001, 0b1001,
        ); //<0..0 1001>
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "&", 0b1000, 0b1101, 0b0100, 0b1101, 0b1001, 0b1011, 0b1001, 0b1001, 0b1101, 0b1101,
            0b1001, 0b1001,
        );
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "|", 0b0000, 0b0101, //<0..0 0*0*>
            0b0100, 0b1101, //<0..0 *10*>
            0b1101, 0b1111, //<0..0 11*1>
            0b0000, 0b0101, //<0..0 0*0*>
            0b1100, 0b1101, //<0..0 110*>
            0b1101, 0b1101,
        ); //<0..0 1101>
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "<<", 0b00001, 0b10111, //<0..0 *0**1>
            0b00010, 0b00010, //<0..0 00010>
            0b01000, 0b11111, //<0..0 *1***>
            0b00011, 0b00111, //<0..0 00*11>
            0b00010, 0b00010, //<0..0 00010>
            0b01100, 0b11100,
        ); //<0..0 *1100>
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "<<", 0b0001, 0b0111, //<0..0 0**1>
            0b0000, 0b0000, //<0..0 0000>
            0b0001, 0b0011, //<0..0 00*1>
            0b0001, 0b0011, //<0..0 00*1>
            0b0000, 0b0000, //<0..0 0000>
            0b0001, 0b0011,
        ); //<0..0 00*1>
        assert_eq!(res.is_ok(), true);
    }

    #[test]
    fn test_decomposed_ite() {
        let res = test_constrain_three_ops(
            "ite", 0b10000, 0b11011, //<0..0 1*0**>
            0b01010, 0b11111, //<0..0 *1*1*>
            0b00000, 0b01110, //<0..0 0***0>
            0b10000, 0b11011, //<0..0 1*0**>
            0b01010, 0b01110, //<0..0 01*10>
            0b01010, 0b01110,
        ); //<0..0 01*10>
        assert_eq!(res.is_ok(), true);
    }

    #[test]
    fn test_decomposed_add() {
        let mut res = test_constrain_three_ops(
            "+", 0b0000, 0b0101, //<0..0 0*0*>
            0b0100, 0b1101, //<0..0 *10*>
            0b0100, 0b1111, //<0..0 *1**>
            0b0000, 0b0001, //<0..0 000*>
            0b0100, 0b1101, //<0..0 *10*>
            0b0100, 0b1111,
        ); //<0..0 *1**>
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "+",
            0b0,
            0b1111111110, //<0..0 0*0*>
            0b0,
            0b1111, //<0..0 ****>
            0b10,
            0b111, //<0..0 *1**>
            0b0,
            0b110, //<0..0 000*>
            0b0,
            0b0111, //<0..0 *10*>
            0b10,
            0b111,
        ); //<0..0 *1**>
        assert_eq!(res.is_ok(), true);
    }

    #[test]
    fn test_decomposed_mult() {
        let mut res = test_constrain_three_ops(
            "*", 0b0011, 0b0011, //<0..0 0011>
            0b0101, 0b0101, //<0..0 0101>
            0b0000, 0b1111, //<0..0 ****>
            0b0011, 0b0011, //<0..0 0011>
            0b0101, 0b0101, //<0..0 0101>
            0b1111, 0b1111,
        ); //<0..0 1111>
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "*", 0b0011, 0b0011, //<0..0 0011>
            0b0000, 0b1111, //<0..0 ****>
            0b1111, 0b1111, //<0..0 1111>
            0b0011, 0b0011, //<0..0 0011>
            0b0101, 0b0101, //<0..0 0101>
            0b1111, 0b1111,
        ); //<0..0 1111>
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "*", 0b0000, 0b1111, //<0..0 ****>
            0b0101, 0b0101, //<0..0 0101>
            0b1111, 0b1111, //<0..0 1111>
            0b0011, 0b0011, //<0..0 0011>
            0b0101, 0b0101, //<0..0 0101>
            0b1111, 0b1111,
        ); //<0..0 1111>
        assert_eq!(res.is_ok(), true);

        res = test_constrain_three_ops(
            "*", 0b0001, 0b0111, //<0..0 0**1>
            0b0100, 0b1101, //<0..0 *10*>
            0b0101, 0b1111, //<0..0 *1*1>
            0b0001, 0b0011, //<0..0 00*1>
            0b0101, 0b1101, //<0..0 *101>
            0b0101, 0b1111,
        ); //<0..0 *1*1>
        assert_eq!(res.is_ok(), true);
    }

    #[test]
    fn test_decomposed_divu() {
        let res = test_constrain_three_ops(
            "/", 0b0010, 0b0111, //<0..0 0*1*>
            0b0000, 0b1110, //<0..0 ***0>
            0b0010, 0b1111, //<0..0 **1*>
            0b0110, 0b0111, //<0..0 011*>
            0b0010, 0b0010, //<0..0 0010>
            0b0011, 0b0011,
        ); //<0..0 0011>
        assert_eq!(res.is_ok(), true);
    }

    #[test]
    fn test_find_next() {
        let x = TritVector::new(0b010, 0b111).expect("new TritVector");

        assert_eq!(x.find_next_higher_match(BitVector(0)).0, BitVector(2));
        assert_eq!(x.find_next_higher_match(BitVector(2)).0, BitVector(2));
        assert_eq!(x.find_next_higher_match(BitVector(4)).0, BitVector(6));
        assert_eq!(x.find_next_higher_match(BitVector(5)).0, BitVector(6));

        assert_eq!(x.find_next_lower_match(BitVector(8)).0, BitVector(7));
        assert_eq!(x.find_next_lower_match(BitVector(7)).0, BitVector(7));
        assert_eq!(x.find_next_lower_match(BitVector(5)).0, BitVector(3));
        assert_eq!(x.find_next_lower_match(BitVector(4)).0, BitVector(3));

        let x = TritVector::new(0b0, 0b1110).expect("new TritVector");
        assert_eq!(
            x.find_next_lower_match(BitVector(0b101)).0,
            BitVector(0b100)
        );
        assert_eq!(
            x.find_next_higher_match(BitVector(0b101)).0,
            BitVector(0b110)
        );

        let x = TritVector::new(0b1, 0b1111).expect("new TritVector");
        assert_eq!(
            x.find_next_lower_match(BitVector(0b100)).0,
            BitVector(0b011)
        );
        assert_eq!(
            x.find_next_lower_match(BitVector(0b110)).0,
            BitVector(0b101)
        );
        assert_eq!(
            x.find_next_higher_match(BitVector(0b100)).0,
            BitVector(0b101)
        );

        let x = TritVector::new(0b10, u64::max_value() - 1).expect("new TritVector");
        assert_eq!(
            x.find_next_lower_match(BitVector(1)).0,
            BitVector(u64::max_value() - 1)
        );
        assert_eq!(
            x.find_next_lower_match(BitVector(0)).0,
            BitVector(u64::max_value() - 1)
        );
        assert_eq!(x.find_next_higher_match(BitVector::ones()).0, BitVector(2));
    }
}

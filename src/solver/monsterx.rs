#![allow(clippy::many_single_char_names)]
#![allow(clippy::if_same_then_else)]
#![allow(clippy::neg_cmp_op_on_partial_ord)]

use super::{
    Assignment, BVOperator, BitVector, CPResult, Formula, OperandSide, Solver, SolverError, Symbol,
    SymbolId, TritVector,
};
use divisors::get_divisors;
use log::{debug, log_enabled, trace, Level};
use rand::{distributions::Uniform, random, seq::SliceRandom, thread_rng, Rng};
use std::time::{Duration, Instant};

pub struct MonsterXSolver {
    timeout: Duration,
}

impl Default for MonsterXSolver {
    fn default() -> Self {
        Self::new(Duration::new(3, 0))
    }
}

impl MonsterXSolver {
    pub fn new(timeout: Duration) -> Self {
        Self { timeout }
    }
}

impl Solver for MonsterXSolver {
    fn name() -> &'static str {
        "MonsterX"
    }

    fn solve_impl<F: Formula>(&self, formula: &F) -> Result<Option<Assignment>, SolverError> {
        let cb = compute_constant_bits(formula)?;

        let ab = initialize_ab(formula, &cb);

        sat(formula, ab, cb, self.timeout)
    }
}

// check if invertibility condition is met considering constant bits in x
fn is_invertible(
    op: BVOperator,
    s: BitVector,
    _x: TritVector,
    t: BitVector,
    d: OperandSide,
) -> bool {
    match op {
        BVOperator::Add => true,
        BVOperator::Sub => true,
        BVOperator::Mul => (-s | s) & t == t,
        BVOperator::Divu => match d {
            OperandSide::Lhs => {
                if (t == BitVector::ones()) && s == BitVector(0) {
                    false
                } else if (t == BitVector::ones()) && (s != BitVector(0)) && (s != BitVector(1)) {
                    false
                } else if (t != BitVector::ones()) && (s == BitVector(0)) {
                    false
                } else {
                    !t.mulo(s)
                }
            }
            OperandSide::Rhs => {
                if (t == s) && (t == BitVector(0)) {
                    false
                } else if (t == BitVector(0)) && (s == BitVector::ones()) {
                    false
                } else {
                    !(s < t)
                }
            }
        },
        BVOperator::Sltu => match d {
            OperandSide::Lhs => {
                if t != BitVector(0) {
                    !(s == BitVector(0))
                } else {
                    true
                }
            }
            OperandSide::Rhs => {
                if t != BitVector(0) {
                    !(s == BitVector::ones())
                } else {
                    true
                }
            }
        },
        BVOperator::Remu => match d {
            OperandSide::Lhs => !(s <= t),
            OperandSide::Rhs => {
                !(s < t) || ((t != BitVector(0)) && t == s - BitVector(1)) || (s - t <= t)
            }
        },
        BVOperator::Not => true,
        BVOperator::BitwiseAnd => (t & s) == t,
        BVOperator::Equals => true,
    }
}

fn is_consistent<F: Formula>(
    f: &F,
    n: SymbolId,
    _x: TritVector,
    _s: TritVector,
    _t: BitVector,
    d: OperandSide,
) -> bool {
    match &f[n] {
        Symbol::Operator(op) => match op {
            BVOperator::Add => true,
            BVOperator::Sub => true,
            BVOperator::Mul => true,
            BVOperator::Divu => match d {
                OperandSide::Lhs => true,
                OperandSide::Rhs => true,
            },
            BVOperator::Sltu => match d {
                OperandSide::Lhs => true,
                OperandSide::Rhs => true,
            },
            BVOperator::Remu => match d {
                OperandSide::Lhs => true,
                OperandSide::Rhs => true,
            },
            BVOperator::Not => true,
            BVOperator::BitwiseAnd => true,
            BVOperator::Equals => true,
        },
        _ => panic!("instruction node expected"),
    }
}

fn compute_constant_bits<F: Formula>(formula: &F) -> Result<Vec<TritVector>, SolverError> {
    // constrains trit vectors corresponding to boolean results to <0,1>
    // initializes inputs to full domain <0..0, 1..1> and root to target value <1,1>
    fn initialize_cb<F: Formula>(formula: &F) -> Vec<TritVector> {
        let max_id = formula
            .symbol_ids()
            .max()
            .expect("formula should not be empty");

        let mut cb = Vec::with_capacity(std::mem::size_of::<TritVector>() * (max_id + 1));
        unsafe {
            cb.set_len(max_id + 1);
        }

        formula.symbol_ids().for_each(|i| {
            cb[i] = match formula[i] {
                Symbol::Input(_) => TritVector::default(),
                Symbol::Constant(c) => TritVector { l: c, u: c },
                Symbol::Operator(o) => match o {
                    BVOperator::Not | BVOperator::Equals | BVOperator::Sltu => {
                        TritVector::new(0, 1).unwrap()
                    }
                    _ => TritVector::default(),
                },
            }
        });

        cb[formula.root()] = TritVector::one();

        if log_enabled!(Level::Trace) {
            formula
                .symbol_ids()
                .filter(|i| matches!(formula[*i], Symbol::Input(_)))
                .for_each(|i| {
                    trace!("initialize: x{} <- <{}, {}>", i, cb[i].l.0, cb[i].u.0);
                });
        }
        cb
    }

    let mut cb = initialize_cb(formula);
    let mut to_be_processed = vec![false; cb.len()];
    let mut stack = vec![formula.root()];
    to_be_processed[formula.root()] = true;

    // propagate until fixpoint is reached
    // a conflict during propagation yields an unsat error
    while let Some(n) = stack.pop() {
        to_be_processed[n] = false;
        match propagate_constraint(formula, &mut cb, n) {
            Ok(None) => continue,
            Ok(Some(updated)) => updated.iter().for_each(|&v| {
                if v == n {
                    formula.dependencies(n).for_each(|i| {
                        if !to_be_processed[i] {
                            stack.push(i);
                            to_be_processed[i] = true;
                        }
                    });
                } else if !to_be_processed[v] {
                    stack.push(v);
                    to_be_processed[v] = true;
                }
            }),
            Err(SolverError::UnSat) => return Err(SolverError::UnSat),
            _ => panic!("unexpected error during constraint propagation"),
        }
    }

    Ok(cb)
}

fn propagate_constraint<F: Formula>(
    f: &F,
    cb: &mut Vec<TritVector>,
    n: SymbolId,
) -> Result<Option<Vec<usize>>, SolverError> {
    // propagate binary/unary constraint and return (possibly) updated trit vectors
    // an unsatisfiable constraint yields an error
    fn constrain_binary<F: Formula>(
        f: &F,
        cb: &mut Vec<TritVector>,
        n: SymbolId,
    ) -> CPResult<(TritVector, TritVector, TritVector)> {
        if let (lhs, Some(rhs)) = f.operands(n) {
            let x = cb[lhs];
            let y = cb[rhs];
            let z = cb[n];

            match &f[n] {
                Symbol::Operator(op) => match op {
                    BVOperator::Add => z.constrain_add(x, y, true),
                    BVOperator::Sub => z.constrain_sub(x, y),
                    BVOperator::Mul => z.constrain_mul(x, y, true),
                    BVOperator::Divu => z.constrain_divu(x, y),
                    BVOperator::BitwiseAnd => z.constrain_and(x, y),
                    BVOperator::Sltu => z.constrain_reif_sltu(x, y),
                    BVOperator::Equals => z.constrain_reif_eq(x, y),
                    _ => Ok((x, y, z)),
                },
                _ => unreachable!("unexpected symbol: {:?}", f[n]),
            }
        } else {
            panic!("can not update binary operator with 1 operand")
        }
    }

    fn constrain_unary<F: Formula>(
        f: &F,
        cb: &mut Vec<TritVector>,
        n: SymbolId,
    ) -> CPResult<(TritVector, TritVector)> {
        if let (p, None) = f.operands(n) {
            let x = cb[p];
            let z = cb[n];

            match &f[n] {
                Symbol::Operator(BVOperator::Not) => z.constrain_not(x),
                _ => unreachable!("unexpected symbol: {:?}", f[n]),
            }
        } else {
            panic!("can not update unary operator with more than one operand")
        }
    }

    // update trit vectors after successful propagation (otherwise SolverError)
    // return modified trit vectors for further propagation
    fn update_binary<F: Formula>(
        f: &F,
        cb: &mut Vec<TritVector>,
        n: SymbolId,
        s: &str,
    ) -> Result<Option<Vec<usize>>, SolverError> {
        if let (lhs, Some(rhs)) = f.operands(n) {
            if let Ok((z, x, y)) = constrain_binary(f, cb, n) {
                debug!(
                    "constrain: x{}({}) := x{}({}) {} x{}({})",
                    n, cb[n], lhs, cb[lhs], s, rhs, cb[rhs]
                );
                debug!(
                    "update with: x{}({}) := x{}({}) {} x{}({})",
                    n, z, lhs, x, s, rhs, y
                );

                let previous = [cb[lhs], cb[rhs], cb[n]];

                cb[n] = z;
                cb[lhs] = x;
                cb[rhs] = y;

                // filter modified trit vectors
                let updated = vec![lhs, rhs, n]
                    .iter()
                    .enumerate()
                    .filter(|(i, &e)| previous[*i] != cb[e])
                    .map(|(_i, &e)| e)
                    .collect();

                Ok(Some(updated))
            } else {
                debug!(
                    "UNSAT constraint found propagating: x{}({}) := x{}({}) {} x{}({})",
                    n, cb[n], lhs, cb[lhs], s, rhs, cb[rhs]
                );

                Err(SolverError::UnSat)
            }
        } else {
            panic!("can not update binary operator with 1 operand")
        }
    }

    fn update_unary<F: Formula>(
        f: &F,
        cb: &mut Vec<TritVector>,
        n: SymbolId,
        s: &str,
    ) -> Result<Option<Vec<usize>>, SolverError> {
        if let (p, None) = f.operands(n) {
            if let Ok((z, x)) = constrain_unary(f, cb, n) {
                debug!("constrain: x{}({}) := {} x{}({})", n, cb[n], s, p, cb[p]);
                debug!("update with: x{}({}) := {} x{}({})", n, z, s, p, x);

                let previous = [cb[p], cb[n]];

                cb[n] = z;
                cb[p] = x;

                let updated = vec![p, n]
                    .iter()
                    .enumerate()
                    .filter(|(i, &e)| previous[*i] != cb[e])
                    .map(|(_i, &e)| e)
                    .collect::<Vec<usize>>();

                Ok(Some(updated))
            } else {
                debug!(
                    "UNSAT constraint found propagating: x{}({}) := {} x{}({})",
                    n, cb[n], s, p, cb[p]
                );
                Err(SolverError::UnSat)
            }
        } else {
            panic!("can not update unary operator with more than one operand")
        }
    }

    match &f[n] {
        Symbol::Constant(_) | Symbol::Input(_) => Ok(None),
        Symbol::Operator(op) => match op {
            BVOperator::Add => update_binary(f, cb, n, "+"),
            BVOperator::Sub => update_binary(f, cb, n, "-"),
            BVOperator::Mul => update_binary(f, cb, n, "*"),
            BVOperator::Divu => update_binary(f, cb, n, "/"),
            BVOperator::BitwiseAnd => update_binary(f, cb, n, "&"),
            BVOperator::Sltu => update_binary(f, cb, n, "<"),
            BVOperator::Remu => update_binary(f, cb, n, "%"),
            BVOperator::Equals => update_binary(f, cb, n, "="),
            BVOperator::Not => update_unary(f, cb, n, "!"),
        },
    }
}

// initialize bit vectors with a consistent initial assignment to the formula
// inputs are initialized with random values matching constant bits
fn initialize_ab<F: Formula>(formula: &F, cb: &[TritVector]) -> Vec<BitVector> {
    // Initialize values for all input/const nodes
    let max_id = formula
        .symbol_ids()
        .max()
        .expect("formula should not be empty");

    let mut ab = Vec::with_capacity(std::mem::size_of::<BitVector>() * (max_id + 1));
    unsafe {
        ab.set_len(max_id + 1);
    }

    formula.symbol_ids().for_each(|i| {
        ab[i] = match formula[i] {
            Symbol::Constant(c) => c,
            _ => cb[i].force_cbs_onto(BitVector(random::<u64>())),
        };
    });

    if log_enabled!(Level::Trace) {
        formula
            .symbol_ids()
            .filter(|i| matches!(formula[*i], Symbol::Input(_)))
            .for_each(|i| {
                trace!("initialize: x{} <- {:#x}", i, ab[i].0);
            });
    }

    // Propagate all values down when all input/const nodes are initialized
    formula.symbol_ids().for_each(|i| match formula[i] {
        Symbol::Input(_) | Symbol::Constant(_) => {
            formula
                .dependencies(i)
                .for_each(|n| propagate_assignment(formula, &mut ab, n));
        }
        _ => {}
    });

    ab
}

// selects a child node to propagate downwards
// always selects an "essential" input if there is one
// otherwise selects an input undeterministically
fn select<F: Formula>(
    f: &F,
    idx: SymbolId,
    t: BitVector,
    ab: &[BitVector],
    cb: &[TritVector],
) -> (SymbolId, SymbolId, OperandSide) {
    if let (lhs, Some(rhs)) = f.operands(idx) {
        fn is_constant<F: Formula>(f: &F, n: SymbolId) -> bool {
            matches!(f[n], Symbol::Constant(_))
        }

        #[allow(clippy::if_same_then_else)]
        if is_constant(f, lhs) {
            (rhs, lhs, OperandSide::Rhs)
        } else if is_constant(f, rhs) {
            (lhs, rhs, OperandSide::Lhs)
        } else if is_essential(f, lhs, OperandSide::Lhs, rhs, t, ab, cb) {
            (lhs, rhs, OperandSide::Lhs)
        } else if is_essential(f, rhs, OperandSide::Rhs, lhs, t, ab, cb) {
            (rhs, lhs, OperandSide::Rhs)
        } else if random() {
            (rhs, lhs, OperandSide::Rhs)
        } else {
            (lhs, rhs, OperandSide::Lhs)
        }
    } else {
        panic!("can only select path for binary operators")
    }
}

fn compute_inverse_value(
    op: BVOperator,
    s: BitVector,
    _x: TritVector,
    t: BitVector,
    d: OperandSide,
) -> BitVector {
    match op {
        BVOperator::Add => t - s,
        BVOperator::Sub => match d {
            OperandSide::Lhs => t + s,
            OperandSide::Rhs => s - t,
        },
        BVOperator::Mul => {
            let y = s >> s.ctz();

            let y_inv = y
                .modinverse()
                .expect("a modular inverse has to exist iff operator is invertible");

            let result = (t >> s.ctz()) * y_inv;

            let to_shift = 64 - s.ctz();

            let arbitrary_bit_mask = if to_shift == 64 {
                BitVector(0)
            } else {
                BitVector::ones() << to_shift
            };

            let arbitrary_bits = BitVector(random::<u64>()) & arbitrary_bit_mask;

            result | arbitrary_bits
        }
        BVOperator::Sltu => match d {
            OperandSide::Lhs => {
                if t == BitVector(0) {
                    // x<s == false; therefore we need a random x>=s
                    BitVector(thread_rng().sample(Uniform::new_inclusive(s.0, BitVector::ones().0)))
                } else {
                    // x<s == true; therefore we need a random x<s
                    BitVector(thread_rng().sample(Uniform::new(0, s.0)))
                }
            }
            OperandSide::Rhs => {
                if t == BitVector(0) {
                    // s<x == false; therefore we need a random x<=s
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, s.0)))
                } else {
                    // s<x == true; therefore we need a random x>s
                    BitVector(
                        thread_rng().sample(Uniform::new_inclusive(s.0 + 1, BitVector::ones().0)),
                    )
                }
            }
        },
        BVOperator::Divu => match d {
            OperandSide::Lhs => {
                if (t == BitVector::ones()) && (s == BitVector(1)) {
                    BitVector::ones()
                } else {
                    let range_start = t * s;
                    if range_start.0.overflowing_add(s.0 - 1).1 {
                        BitVector(
                            thread_rng()
                                .sample(Uniform::new_inclusive(range_start.0, u64::max_value())),
                        )
                    } else {
                        BitVector(thread_rng().sample(Uniform::new_inclusive(
                            range_start.0,
                            range_start.0 + (s.0 - 1),
                        )))
                    }
                }
            }
            OperandSide::Rhs => {
                if (t == s) && t == BitVector::ones() {
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, 1)))
                } else if (t == BitVector::ones()) && (s != BitVector::ones()) {
                    BitVector(0)
                } else {
                    s / t
                }
            }
        },
        BVOperator::Remu => match d {
            OperandSide::Lhs => {
                let y = BitVector(
                    thread_rng().sample(Uniform::new_inclusive(1, ((BitVector::ones() - t) / s).0)),
                );
                // below computation cannot overflow due to how `y` was chosen
                assert!(
                    !s.0.overflowing_mul(y.0).1,
                    "multiplication overflow in REMU inverse"
                );
                assert!(
                    !t.0.overflowing_add(y.0 * s.0).1,
                    "addition overflow in REMU inverse"
                );
                y * s + t
            }
            OperandSide::Rhs => {
                if s == t {
                    let x = BitVector(
                        thread_rng().sample(Uniform::new_inclusive(t.0, BitVector::ones().0)),
                    );
                    if x == t {
                        BitVector(0)
                    } else {
                        x
                    }
                } else {
                    let mut v = get_divisors(s.0 - t.0);
                    v.push(1);
                    v.push(s.0 - t.0);
                    v = v.into_iter().filter(|x| x > &t.0).collect();

                    BitVector(*v.choose(&mut rand::thread_rng()).unwrap())
                }
            }
        },
        BVOperator::BitwiseAnd => BitVector(random::<u64>()) | t,
        BVOperator::Equals => {
            if t == BitVector(0) {
                loop {
                    let r = BitVector(random::<u64>());
                    if r != s {
                        break r;
                    }
                }
            } else {
                s
            }
        }
        _ => unreachable!("unknown operator or unary operator: {:?}", op),
    }
}

fn compute_consistent_value(
    op: BVOperator,
    _x: TritVector,
    t: BitVector,
    d: OperandSide,
) -> BitVector {
    match op {
        BVOperator::Add | BVOperator::Sub | BVOperator::Equals => BitVector(random::<u64>()),
        BVOperator::Mul => BitVector({
            if t == BitVector(0) {
                0
            } else {
                let mut r;
                loop {
                    r = random::<u128>();
                    if r != 0 {
                        break;
                    }
                }
                if t.ctz() < r.trailing_zeros() {
                    r >>= r.trailing_zeros() - t.ctz();
                }
                assert!(t.ctz() >= r.trailing_zeros());
                r as u64
            }
        }),
        BVOperator::Divu => match d {
            OperandSide::Lhs => {
                if (t == BitVector::ones()) || (t == BitVector(0)) {
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, u64::max_value() - 1)))
                } else {
                    let mut y = BitVector(0);
                    while !(y != BitVector(0)) && !(y.mulo(t)) {
                        y = BitVector(
                            thread_rng().sample(Uniform::new_inclusive(0, u64::max_value())),
                        );
                    }

                    y * t
                }
            }
            OperandSide::Rhs => {
                if t == BitVector::ones() {
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, 1)))
                } else {
                    BitVector(
                        thread_rng().sample(Uniform::new_inclusive(0, u64::max_value() / t.0)),
                    )
                }
            }
        },
        BVOperator::Sltu => match d {
            OperandSide::Lhs => {
                if t == BitVector(0) {
                    // x<s == false
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, BitVector::ones().0)))
                } else {
                    // x<s == true
                    BitVector(thread_rng().sample(Uniform::new(0, BitVector::ones().0)))
                }
            }
            OperandSide::Rhs => {
                if t == BitVector(0) {
                    // s<x == false
                    BitVector(thread_rng().sample(Uniform::new_inclusive(0, BitVector::ones().0)))
                } else {
                    // s<x == true
                    BitVector(thread_rng().sample(Uniform::new(1, BitVector::ones().0)))
                }
            }
        },
        BVOperator::Remu => match d {
            OperandSide::Lhs => {
                if t == BitVector::ones() {
                    BitVector::ones()
                } else {
                    BitVector(thread_rng().sample(Uniform::new_inclusive(t.0, BitVector::ones().0)))
                }
            }
            OperandSide::Rhs => {
                if t == BitVector::ones() {
                    BitVector(0)
                } else {
                    BitVector(
                        thread_rng().sample(Uniform::new_inclusive(t.0 + 1, BitVector::ones().0)),
                    )
                }
            }
        },
        BVOperator::BitwiseAnd => BitVector(random::<u64>()) | t,
        _ => unreachable!("unknown operator for consistent value: {:?}", op),
    }
}

fn compute_inverse_value_for_unary_op(op: BVOperator, t: BitVector) -> BitVector {
    match op {
        BVOperator::Not => {
            if t == BitVector(0) {
                BitVector(1)
            } else {
                BitVector(0)
            }
        }
        _ => unreachable!("not unary operator: {:?}", op),
    }
}

const CHOOSE_INVERSE: f64 = 0.90;

// computes an inverse/consistent target value
#[allow(clippy::too_many_arguments)]
fn value<F: Formula>(
    f: &F,
    n: SymbolId,
    ns: SymbolId,
    side: OperandSide,
    x: TritVector,
    t: BitVector,
    ab: &[BitVector],
) -> BitVector {
    let s = ab[ns];

    match &f[n] {
        Symbol::Operator(op) => {
            let consistent = compute_consistent_value(*op, x, t, side);

            if is_invertible(*op, s, x, t, side) {
                let inverse = compute_inverse_value(*op, s, x, t, side);
                let choose_inverse =
                    rand::thread_rng().gen_range(0.0_f64..=1.0_f64) < CHOOSE_INVERSE;

                if choose_inverse {
                    inverse
                } else {
                    consistent
                }
            } else {
                consistent
            }
        }
        _ => unimplemented!(),
    }
}

fn is_essential<F: Formula>(
    formula: &F,
    this: SymbolId,
    on_side: OperandSide,
    other: SymbolId,
    t: BitVector,
    ab: &[BitVector],
    cb: &[TritVector],
) -> bool {
    let ab_nx = ab[this];

    match &formula[other] {
        Symbol::Operator(op) => !is_invertible(*op, ab_nx, cb[other], t, on_side.other()),
        // TODO: not mentioned in paper => improvised. is that really true?
        Symbol::Constant(_) | Symbol::Input(_) => false,
    }
}

fn update_assignment<F: Formula>(f: &F, ab: &mut Vec<BitVector>, n: SymbolId, v: BitVector) {
    ab[n] = v;

    assert!(
        matches!(f[n], Symbol::Input(_)),
        "only inputs can be assigned"
    );

    trace!("update: x{} <- {:#x}", n, v.0);

    f.dependencies(n)
        .for_each(|n| propagate_assignment(f, ab, n));
}

fn propagate_assignment<F: Formula>(f: &F, ab: &mut Vec<BitVector>, n: SymbolId) {
    fn update_binary<F: Formula, Op>(f: &F, ab: &mut Vec<BitVector>, n: SymbolId, s: &str, op: Op)
    where
        Op: FnOnce(BitVector, BitVector) -> BitVector,
    {
        if let (lhs, Some(rhs)) = f.operands(n) {
            let result = op(ab[lhs], ab[rhs]);

            trace!(
                "propagate: x{} := x{}({:#x}) {} x{}({:#x}) |- x{} <- {:#x}",
                n,
                lhs,
                ab[lhs].0,
                s,
                rhs,
                ab[rhs].0,
                n,
                result.0
            );

            ab[n] = result;
        } else {
            panic!("can not update binary operator with 1 operand")
        }
    }

    fn update_unary<F: Formula, Op>(f: &F, ab: &mut Vec<BitVector>, n: SymbolId, s: &str, op: Op)
    where
        Op: FnOnce(BitVector) -> BitVector,
    {
        if let (p, None) = f.operands(n) {
            let result = op(ab[p]);

            trace!(
                "propagate: x{} := {}x{}({:#x}) |- x{} <- {:#x}",
                n,
                s,
                p,
                ab[p].0,
                n,
                result.0
            );

            ab[n] = result;
        } else {
            panic!("can not update unary operator with more than one operand")
        }
    }

    match &f[n] {
        Symbol::Operator(op) => {
            match op {
                BVOperator::Add => update_binary(f, ab, n, "+", |l, r| l + r),
                BVOperator::Sub => update_binary(f, ab, n, "-", |l, r| l - r),
                BVOperator::Mul => update_binary(f, ab, n, "*", |l, r| l * r),
                BVOperator::Divu => update_binary(f, ab, n, "/", |l, r| l / r),
                BVOperator::BitwiseAnd => update_binary(f, ab, n, "&", |l, r| l & r),
                BVOperator::Sltu => update_binary(f, ab, n, "<", |l, r| {
                    if l < r {
                        BitVector(1)
                    } else {
                        BitVector(0)
                    }
                }),
                BVOperator::Remu => update_binary(f, ab, n, "%", |l, r| l % r),
                BVOperator::Equals => update_binary(f, ab, n, "=", |l, r| {
                    if l == r {
                        BitVector(1)
                    } else {
                        BitVector(0)
                    }
                }),
                BVOperator::Not => update_unary(f, ab, n, "!", |x| {
                    if x == BitVector(0) {
                        BitVector(1)
                    } else {
                        BitVector(0)
                    }
                }),
            }
            f.dependencies(n)
                //f.neighbors_directed(n, Direction::Outgoing)
                .for_each(|n| propagate_assignment(f, ab, n));
        }
        _ => unreachable!(),
    }
}

// can only handle one Equals constraint with constant
fn sat<F: Formula>(
    formula: &F,
    mut ab: Vec<BitVector>,
    cb: Vec<TritVector>,
    timeout_time: Duration,
) -> Result<Option<Assignment>, SolverError> {
    let mut iterations = 0;

    let start_time = Instant::now();

    let root = formula.root();

    while ab[root] != BitVector(1) {
        let mut n = root;
        let mut t = BitVector(1);

        iterations += 1;
        trace!("search {}: x{} <- 0x1", iterations, root);

        while !formula.is_operand(n) {
            if start_time.elapsed() > timeout_time {
                return Err(SolverError::Timeout);
            }
            let (v, nx) = match formula[n] {
                Symbol::Operator(op) => {
                    if op.is_unary() {
                        let nx = formula.operand(n);

                        let v = compute_inverse_value_for_unary_op(op, t);

                        trace!(
                            "search {}: x{}({:#x}) = {}x{}({:#x}) |- x{} <- {:#x}",
                            iterations,
                            n,
                            t.0,
                            op,
                            nx,
                            ab[nx].0,
                            nx,
                            v.0
                        );

                        (v, nx)
                    } else {
                        let (nx, ns, side) = select(formula, n, t, &ab, &cb);

                        if !is_consistent(formula, n, cb[nx], cb[ns], t, side) {
                            trace!("aborting search - inconsistency found");
                            break;
                        }

                        let v = value(formula, n, ns, side, cb[nx], t, &ab);

                        if log_enabled!(Level::Trace) {
                            let (lhs, rhs) = if side == OperandSide::Lhs {
                                (nx, ns)
                            } else {
                                (ns, nx)
                            };

                            trace!(
                                "search {}: x{}({:#x}) := x{}({:#x}) {} x{}({:#x}) |- x{} <- {:#x}",
                                iterations,
                                n,
                                t.0,
                                lhs,
                                ab[lhs].0,
                                op,
                                rhs,
                                ab[rhs].0,
                                nx,
                                v.0
                            );
                        }

                        (v, nx)
                    }
                }
                _ => panic!("non instruction node found"),
            };

            t = v;
            n = nx;
        }

        update_assignment(formula, &mut ab, n, t);
    }

    let assignment: Assignment = formula.symbol_ids().map(|i| (i, ab[i])).collect();

    Ok(Some(assignment))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::symbolic_state::{DataFlowGraph, FormulaView, SymbolicValue};
    use crate::solver::*;

    fn create_data_flow_with_input() -> (DataFlowGraph, SymbolicValue) {
        let mut formula = DataFlowGraph::new();

        let input = Symbol::Input(String::from("x0"));
        let input_idx = formula.add_node(input);

        (formula, input_idx)
    }

    fn add_equals_constraint(
        data_flow: &mut DataFlowGraph,
        to: SymbolicValue,
        on: OperandSide,
        constant: u64,
    ) -> SymbolicValue {
        let constrain = Symbol::Operator(BVOperator::Equals);
        let constrain_idx = data_flow.add_node(constrain);

        let constrain_c = Symbol::Constant(BitVector(constant));
        let constrain_c_idx = data_flow.add_node(constrain_c);

        data_flow.add_edge(to, constrain_idx, on);
        data_flow.add_edge(constrain_c_idx, constrain_idx, on.other());

        constrain_idx
    }

    #[test]
    fn solve_trivial_equals_constraint() {
        let (mut data_flow, input_idx) = create_data_flow_with_input();

        let root = add_equals_constraint(&mut data_flow, input_idx, OperandSide::Lhs, 10);

        let solver = MonsterXSolver::default();
        let formula = FormulaView::new(&data_flow, root);
        let result = solver.solve(&formula);

        assert!(result.is_ok(), "solver did not time out");
        let unwrapped_result = result.unwrap();

        assert!(
            unwrapped_result.is_some(),
            "has result for trivial equals constraint"
        );
        assert_eq!(
            *unwrapped_result.unwrap().get(&input_idx.index()).unwrap(),
            BitVector(10),
            "solver result of trivial equal constrain has right value"
        );
    }

    #[test]
    fn solve_bvadd() {
        let (mut data_flow, input_idx) = create_data_flow_with_input();

        let constant = Symbol::Constant(BitVector(3));
        let constant_idx = data_flow.add_node(constant);

        let instr = Symbol::Operator(BVOperator::Add);
        let instr_idx = data_flow.add_node(instr);

        data_flow.add_edge(input_idx, instr_idx, OperandSide::Lhs);
        data_flow.add_edge(constant_idx, instr_idx, OperandSide::Rhs);

        let root = add_equals_constraint(&mut data_flow, instr_idx, OperandSide::Lhs, 10);

        let solver = MonsterXSolver::default();
        let formula = FormulaView::new(&data_flow, root);
        let result = solver.solve(&formula);

        assert!(result.is_ok(), "solver did not time out");
        let unwrapped_result = result.unwrap();

        assert!(unwrapped_result.is_some(), "has result for trivial add op");
        assert_eq!(
            *unwrapped_result.unwrap().get(&input_idx.index()).unwrap(),
            BitVector(7),
            "solver result of trivial add op has right value"
        );
    }

    fn test_invertibility(
        op: BVOperator,
        s: u64,
        t: u64,
        d: OperandSide,
        result: bool,
        msg: &'static str,
    ) {
        let s = BitVector(s);
        let t = BitVector(t);
        let x = TritVector::default();

        match d {
            OperandSide::Lhs => {
                assert_eq!(
                    is_invertible(op, s, x, t, d),
                    result,
                    "x {:?} {:?} == {:?}   {}",
                    op,
                    s,
                    t,
                    msg
                );
            }
            OperandSide::Rhs => {
                assert_eq!(
                    is_invertible(op, s, x, t, d),
                    result,
                    "{:?} {:?} x == {:?}   {}",
                    s,
                    op,
                    t,
                    msg
                );
            }
        }
    }

    fn test_inverse_value_computation<F>(op: BVOperator, s: u64, t: u64, d: OperandSide, f: F)
    where
        F: FnOnce(BitVector, BitVector) -> BitVector,
    {
        let s = BitVector(s);
        let t = BitVector(t);
        let x = TritVector::default();

        let computed = compute_inverse_value(op, s, x, t, d);

        // prove: computed <> s == t        where <> is the binary operator

        match d {
            OperandSide::Lhs => {
                assert_eq!(
                    f(computed, s),
                    t,
                    "{:?} {:?} {:?} == {:?}",
                    computed,
                    op,
                    s,
                    t
                );
            }
            OperandSide::Rhs => {
                assert_eq!(
                    f(s, computed),
                    t,
                    "{:?} {:?} {:?} == {:?}",
                    s,
                    op,
                    computed,
                    t
                );
            }
        }
    }

    fn test_consistent_value_computation<F>(op: BVOperator, t: u64, d: OperandSide, f: F)
    where
        F: FnOnce(BitVector, BitVector) -> BitVector,
    {
        let t = BitVector(t);
        let x = TritVector::default();

        let computed = compute_consistent_value(op, x, t, d);

        // TODO: How to test consistent values?
        // To proof that there exists a y, we would have to compute and inverse value, which is not
        // always possible.
        // I think, Alastairs
        // prove: Ey.(computed <> y == t)        where <> is the binary bit vector operator
        //

        let inverse = match op {
            BVOperator::Add => t - computed,
            BVOperator::Mul => {
                assert!(
                    is_invertible(op, computed, x, t, d),
                    "choose values which are invertible..."
                );

                compute_inverse_value(op, computed, x, t, d)
            }
            BVOperator::Sltu => compute_inverse_value(op, computed, x, t, d),
            BVOperator::Divu => {
                assert!(is_invertible(op, computed, x, t, d));
                compute_inverse_value(op, computed, x, t, d)
            }
            _ => unimplemented!(),
        };

        if d == OperandSide::Lhs {
            assert_eq!(
                f(inverse, computed),
                t,
                "{:?} {:?} {:?} == {:?}",
                inverse,
                op,
                computed,
                t
            );
        } else {
            assert_eq!(
                f(computed, inverse),
                t,
                "{:?} {:?} {:?} == {:?}",
                computed,
                op,
                inverse,
                t
            );
        }
    }

    // TODO: add tests for ADD
    // TODO: add tests for SUB

    const MUL: BVOperator = BVOperator::Mul;
    const SLTU: BVOperator = BVOperator::Sltu;
    const DIVU: BVOperator = BVOperator::Divu;
    const REMU: BVOperator = BVOperator::Remu;

    #[test]
    fn check_invertability_condition_for_divu() {
        test_invertibility(DIVU, 0b1, 0b1, OperandSide::Lhs, true, "trivial divu");
        test_invertibility(DIVU, 0b1, 0b1, OperandSide::Rhs, true, "trivial divu");

        test_invertibility(DIVU, 3, 2, OperandSide::Lhs, true, "x / 3 = 2");
        test_invertibility(DIVU, 6, 2, OperandSide::Rhs, true, "6 / x = 2");

        test_invertibility(DIVU, 0, 2, OperandSide::Lhs, false, "x / 0 = 2");
        test_invertibility(DIVU, 0, 2, OperandSide::Rhs, false, "0 / x = 2");

        test_invertibility(DIVU, 5, 6, OperandSide::Rhs, false, "5 / x = 6");
    }

    #[test]
    fn check_invertability_condition_for_mul() {
        let side = OperandSide::Lhs;

        test_invertibility(MUL, 0b1, 0b1, side, true, "trivial multiplication");
        test_invertibility(MUL, 0b10, 0b1, side, false, "operand bigger than result");
        test_invertibility(
            MUL,
            0b10,
            0b10,
            side,
            true,
            "operand with undetermined bits and possible invsere",
        );
        test_invertibility(
            MUL,
            0b10,
            0b10,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
        test_invertibility(
            MUL,
            0b100,
            0b100,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
        test_invertibility(
            MUL,
            0b10,
            0b1100,
            side,
            true,
            "operand with undetermined bits and no inverse value",
        );
    }

    #[test]
    fn check_invertability_condition_for_sltu() {
        let mut side = OperandSide::Lhs;

        test_invertibility(SLTU, 0, 1, side, false, "x < 0 == 1 FALSE");
        test_invertibility(SLTU, 1, 1, side, true, "x < 1 == 1 TRUE");
        test_invertibility(
            SLTU,
            u64::max_value(),
            0,
            side,
            true,
            "x < max_value == 0 TRUE",
        );

        side = OperandSide::Rhs;

        test_invertibility(SLTU, 0, 1, side, true, "0 < x == 1 TRUE");
        test_invertibility(SLTU, 0, 0, side, true, "0 < x == 0 TRUE");
        test_invertibility(
            SLTU,
            u64::max_value(),
            1,
            side,
            false,
            "max_value < x == 1 FALSE",
        );
        test_invertibility(
            SLTU,
            u64::max_value(),
            0,
            side,
            true,
            "max_value < x == 0 TRUE",
        );
    }

    #[test]
    fn compute_inverse_values_for_mul() {
        let side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            l * r
        }

        // test only for values which are actually invertible
        test_inverse_value_computation(MUL, 0b1, 0b1, side, f);
        test_inverse_value_computation(MUL, 0b10, 0b10, side, f);
        test_inverse_value_computation(MUL, 0b100, 0b100, side, f);
        test_inverse_value_computation(MUL, 0b10, 0b1100, side, f);
    }

    #[test]
    fn compute_inverse_values_for_sltu() {
        let mut side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            if l < r {
                BitVector(1)
            } else {
                BitVector(0)
            }
        }

        // test only for values which are actually invertible
        test_inverse_value_computation(SLTU, u64::max_value(), 0, side, f);
        test_inverse_value_computation(SLTU, 0, 0, side, f);
        test_inverse_value_computation(SLTU, 1, 1, side, f);

        side = OperandSide::Rhs;

        test_inverse_value_computation(SLTU, 0, 0, side, f);
        test_inverse_value_computation(SLTU, u64::max_value() - 1, 1, side, f);
        test_inverse_value_computation(SLTU, 1, 1, side, f);
    }

    #[test]
    fn compute_inverse_values_for_divu() {
        fn f(l: BitVector, r: BitVector) -> BitVector {
            l / r
        }

        // test only for values which are actually invertible
        test_inverse_value_computation(DIVU, 0b1, 0b1, OperandSide::Lhs, f);
        test_inverse_value_computation(DIVU, 0b1, 0b1, OperandSide::Rhs, f);

        test_inverse_value_computation(DIVU, 2, 3, OperandSide::Lhs, f);
        test_inverse_value_computation(DIVU, 6, 2, OperandSide::Rhs, f);
    }

    #[test]
    fn compute_inverse_values_for_remu() {
        fn f(l: BitVector, r: BitVector) -> BitVector {
            l % r
        }

        // test only for values which are actually invertible
        test_inverse_value_computation(REMU, u64::max_value(), 0, OperandSide::Lhs, f);
        test_inverse_value_computation(
            REMU,
            u64::max_value() - 1,
            u64::max_value() - 1,
            OperandSide::Rhs,
            f,
        );
        test_inverse_value_computation(REMU, 3, 2, OperandSide::Lhs, f);
        test_inverse_value_computation(REMU, 5, 2, OperandSide::Rhs, f);
    }

    #[test]
    fn compute_consistent_values_for_mul() {
        let side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            l * r
        }

        // test only for values which actually have a consistent value
        test_consistent_value_computation(MUL, 0b110, side, f);
        test_consistent_value_computation(MUL, 0b101, side, f);
        test_consistent_value_computation(MUL, 0b11, side, f);
        test_consistent_value_computation(MUL, 0b100, side, f);
    }

    #[test]
    fn compute_consistent_values_for_sltu() {
        let mut side = OperandSide::Lhs;

        fn f(l: BitVector, r: BitVector) -> BitVector {
            if l < r {
                BitVector(1)
            } else {
                BitVector(0)
            }
        }

        // test only for values which actually have a consistent value
        test_consistent_value_computation(SLTU, 0, side, f);
        test_consistent_value_computation(SLTU, 1, side, f);

        side = OperandSide::Rhs;

        // test only for values which actually have a consistent value
        test_consistent_value_computation(SLTU, 0, side, f);
        test_consistent_value_computation(SLTU, 1, side, f);
    }
}

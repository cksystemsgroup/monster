use crate::modeler::bitblasting::BitBlasting;
use crate::modeler::bitblasting::HashableGateRef;
use crate::modeler::bitblasting::{Gate, GateRef};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

pub type QubitRef = Rc<RefCell<Qubit>>;

// public interface

pub fn call_qubot<'a>(model: &'a BitBlasting<'a>, bad_states: &[GateRef]) -> Vec<QubitRef> {
    // returns qubits of bad states
    let mut qubo = Qubot::new(model);
    qubo.build_qubo(bad_states)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Qubit {}

impl From<Qubit> for QubitRef {
    fn from(qubit: Qubit) -> Self {
        Rc::new(RefCell::new(qubit))
    }
}

#[derive(Debug)]
pub struct HashableQubitRef {
    value: QubitRef,
}

impl Eq for HashableQubitRef {}

impl PartialEq for HashableQubitRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}

impl From<QubitRef> for HashableQubitRef {
    fn from(qubit: QubitRef) -> Self {
        Self { value: qubit }
    }
}

impl Hash for HashableQubitRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

pub struct Qubo {
    linear_coefficients: HashMap<HashableQubitRef, f32>,
    quadratic_coefficients: HashMap<HashableQubitRef, HashMap<HashableQubitRef, f32>>,
    offset: f32,
}

impl Qubo {
    pub fn new() -> Self {
        Self {
            linear_coefficients: HashMap::new(),
            quadratic_coefficients: HashMap::new(),
            offset: 0.0,
        }
    }
    pub fn add_linear_coeff(&mut self, qubit: &QubitRef, value: f32) {
        if value == 0.0 {
            return;
        }
        let key = HashableQubitRef::from(qubit.clone());
        if self.linear_coefficients.contains_key(&key) {
            let new_coeff = self.linear_coefficients.get(&key).unwrap() + value;
            self.linear_coefficients.insert(key, new_coeff);
        } else {
            self.linear_coefficients.insert(key, value);
        }
    }
    fn add_new_row(&mut self, qubit: &QubitRef) {
        let key = HashableQubitRef::from(qubit.clone());
        self.quadratic_coefficients
            .entry(key)
            .or_insert_with(HashMap::new);
    }

    pub fn add_quadratic_coeffs(&mut self, qubit1: &QubitRef, qubit2: &QubitRef, value: f32) {
        if value == 0.0 {
            return;
        }
        let key1;
        let key2;
        match qubit1.as_ptr().cmp(&qubit2.as_ptr()) {
            Ordering::Greater => {
                key1 = HashableQubitRef::from(qubit2.clone());
                key2 = HashableQubitRef::from(qubit1.clone());
                self.add_new_row(&qubit2);
            }
            Ordering::Less => {
                key1 = HashableQubitRef::from(qubit1.clone());
                key2 = HashableQubitRef::from(qubit2.clone());
                self.add_new_row(&qubit1);
            }
            Ordering::Equal => return self.add_linear_coeff(qubit1, value),
        }

        let hashmap: &mut HashMap<HashableQubitRef, f32> =
            self.quadratic_coefficients.get_mut(&key1).unwrap();

        if hashmap.contains_key(&key2) {
            let new_coeff = value + hashmap.get(&key2).unwrap();
            hashmap.insert(key2, new_coeff);
        } else {
            hashmap.insert(key2, value);
        }
    }

    pub fn add_offset(&mut self, value: f32) -> f32 {
        self.offset += value;
        self.offset
    }
}

pub struct Qubot<'a> {
    qubo: Qubo,
    mapping: HashMap<HashableGateRef, QubitRef>,
    mapping_carries: HashMap<HashableGateRef, QubitRef>, // ResultHalfAdder or ResultFullAdder -> to Qubit that represent carries
    const_true_qubit: QubitRef,
    const_false_qubit: QubitRef,
    bitblasting: &'a BitBlasting<'a>,
}

impl<'a> Qubot<'a> {
    pub fn new(model: &'a BitBlasting<'a>) -> Self {
        Self {
            qubo: Qubo::new(),
            mapping: HashMap::new(),
            mapping_carries: HashMap::new(),
            const_true_qubit: QubitRef::new(RefCell::new(Qubit {})),
            const_false_qubit: QubitRef::new(RefCell::new(Qubit {})),
            bitblasting: model,
        }
    }

    fn update_mapping_carries(&mut self, gate: &GateRef, qubit_carry: QubitRef) {
        let key = HashableGateRef::from(gate.clone());
        assert!(!self.mapping_carries.contains_key(&key));
        self.mapping_carries.insert(key, qubit_carry);
    }

    fn query_existence(&self, gate: &GateRef) -> Option<QubitRef> {
        let key = HashableGateRef::from(gate.clone());
        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned()
        } else {
            None
        }
    }

    fn visit(&mut self, gate: &GateRef) -> QubitRef {
        let key = HashableGateRef::from(gate.clone());

        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned().unwrap()
        } else {
            let replacement = self.process_gate(gate);
            assert!(!self.mapping.contains_key(&key));
            replacement
        }
    }

    fn process_gate(&mut self, gate: &GateRef) -> QubitRef {
        if let Some(replacement) = self.query_existence(gate) {
            return replacement;
        }

        match &*gate.borrow() {
            Gate::ConstTrue {} => self.const_true_qubit.clone(),
            Gate::ConstFalse {} => self.const_false_qubit.clone(),
            Gate::InputBit {} => QubitRef::from(RefCell::new(Qubit {})),
            Gate::Not { value } => {
                let operand = self.visit(value);
                let result_qubit = QubitRef::from(Qubit {});
                self.qubo.add_linear_coeff(&operand, -2.0);
                self.qubo.add_linear_coeff(&result_qubit, -2.0);

                self.qubo.add_quadratic_coeffs(&operand, &result_qubit, 4.0);
                self.qubo.add_offset(2.0);
                result_qubit
            }
            Gate::And { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, 0.0);
                self.qubo.add_linear_coeff(&x2, 0.0);
                self.qubo.add_linear_coeff(&z, 6.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_offset(0.0);
                z
            }
            Gate::Nand { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, -4.0);
                self.qubo.add_linear_coeff(&x2, -4.0);
                self.qubo.add_linear_coeff(&z, -6.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, 4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, 4.0);

                self.qubo.add_offset(6.0);
                z
            }
            Gate::Matriarch1 { cond, right } => {
                let x1 = self.visit(cond);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, 0.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, -2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, 4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_offset(0.0);
                z
            }
            Gate::Or { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, 2.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_offset(0.0);
                z
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let x1 = self.visit(input1);
                let x2 = self.visit(input2);

                let aux = QubitRef::from(Qubit {});
                let carry = QubitRef::from(Qubit {});
                let z = QubitRef::from(Qubit {});

                self.update_mapping_carries(gate, carry.clone());

                self.qubo.add_linear_coeff(&x1, 2.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);
                self.qubo.add_linear_coeff(&aux, 4.0);
                self.qubo.add_linear_coeff(&carry, 4.0);

                self.qubo.add_quadratic_coeffs(&carry, &aux, 4.0);
                self.qubo.add_quadratic_coeffs(&x1, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &aux, 4.0);
                self.qubo.add_quadratic_coeffs(&x2, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &x2, 0.0);
                self.qubo.add_quadratic_coeffs(&z, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&z, &carry, 4.0);
                self.qubo.add_quadratic_coeffs(&x1, &z, 0.0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4.0);

                self.qubo.add_offset(0.0);
                z
            }
            Gate::ResultFullAdder {
                input1,
                input2,
                input3,
            } => {
                let x1 = self.visit(input1);
                let x2 = self.visit(input2);
                let x3 = self.visit(input3);

                let aux = QubitRef::from(Qubit {});
                let carry = QubitRef::from(Qubit {});
                let z = QubitRef::from(Qubit {});

                self.update_mapping_carries(gate, carry.clone());

                self.qubo.add_linear_coeff(&x1, 2.0);
                self.qubo.add_linear_coeff(&x2, 2.0);
                self.qubo.add_linear_coeff(&x3, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);
                self.qubo.add_linear_coeff(&aux, 4.0);
                self.qubo.add_linear_coeff(&carry, 4.0);

                self.qubo.add_quadratic_coeffs(&x1, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&x2, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&x1, &x2, 4.0);
                self.qubo.add_quadratic_coeffs(&x3, &aux, 4.0);
                self.qubo.add_quadratic_coeffs(&x3, &carry, -4.0);
                self.qubo.add_quadratic_coeffs(&z, &aux, -4.0);
                self.qubo.add_quadratic_coeffs(&z, &carry, 4.0);
                self.qubo.add_quadratic_coeffs(&z, &x3, -4.0);

                self.qubo.add_offset(0.0);
                z
            }
            Gate::CarryHalfAdder { .. } => {
                let key = HashableGateRef::from(gate.clone());
                let gate_half_adder = self.bitblasting.mapping_adders.get(&key).unwrap();
                self.visit(gate_half_adder);

                let half_adder_key = HashableGateRef::from(gate_half_adder.clone());
                (*self.mapping_carries.get(&half_adder_key).unwrap()).clone()
            }
            Gate::CarryFullAdder { .. } => {
                let key = HashableGateRef::from(gate.clone());
                let gate_full_adder = self.bitblasting.mapping_adders.get(&key).unwrap();
                self.visit(gate_full_adder);

                let full_adder_key = HashableGateRef::from(gate_full_adder.clone());
                (*self.mapping_carries.get(&full_adder_key).unwrap()).clone()
            }
        }
    }

    pub fn build_qubo(&mut self, bad_state_gates: &[GateRef]) -> Vec<QubitRef> {
        let mut bad_state_qubits: Vec<QubitRef> = Vec::new();

        for gate in bad_state_gates {
            bad_state_qubits.push(self.process_gate(gate));
        }

        // or bad states
        if !bad_state_qubits.is_empty() {
            let mut ored_bad_states = bad_state_qubits[0].clone();

            for qubit in bad_state_qubits.iter().skip(1) {
                // or bad state
                let z = QubitRef::from(Qubit {});
                self.qubo.add_linear_coeff(&ored_bad_states, 2.0);
                self.qubo.add_linear_coeff(qubit, 2.0);
                self.qubo.add_linear_coeff(&z, 2.0);

                self.qubo.add_quadratic_coeffs(&ored_bad_states, qubit, 2.0);
                self.qubo.add_quadratic_coeffs(&ored_bad_states, &z, -4.0);
                self.qubo.add_quadratic_coeffs(qubit, &z, -4.0);
                ored_bad_states = z;
            }
        }

        // apply constraints

        bad_state_qubits
    }
}

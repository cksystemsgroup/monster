use crate::modeler::bitblasting::BitBlasting;
use crate::modeler::bitblasting::HashableGateRef;
use crate::modeler::bitblasting::{Gate, GateRef};
use crate::modeler::NodeRef;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

pub type QubitRef = Rc<RefCell<Qubit>>;

// public interface

pub fn call_qubot<'a>(model: &'a BitBlasting<'a>, bad_states: &[GateRef]) -> Vec<QubitRef> {
    // returns qubits of bad states
    let mut qubo = Qubot::new(model);
    qubo.evaluate_inputs(bad_states, &[1, 2, 3]);
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
    linear_coefficients: HashMap<HashableQubitRef, i32>,
    quadratic_coefficients: HashMap<HashableQubitRef, HashMap<HashableQubitRef, i32>>,
    offset: i32,
}

impl Qubo {
    pub fn new() -> Self {
        Self {
            linear_coefficients: HashMap::new(),
            quadratic_coefficients: HashMap::new(),
            offset: 0,
        }
    }

    pub fn _get_count_variables(&mut self) -> usize {
        let set1: HashSet<usize> = self
            .linear_coefficients
            .keys()
            .map(|x| (*x).value.as_ptr() as usize)
            .collect();
        let set2: HashSet<usize> = self
            .quadratic_coefficients
            .keys()
            .map(|x| (*x).value.as_ptr() as usize)
            .collect();

        set1.union(&set2).count()
    }
    pub fn add_linear_coeff(&mut self, qubit: &QubitRef, value: i32) {
        if value == 0 {
            return;
        }
        let key = HashableQubitRef::from(qubit.clone());
        let entry = self.linear_coefficients.entry(key).or_insert(0);
        *entry += value;
    }

    fn add_new_row(&mut self, qubit: &QubitRef) {
        let key = HashableQubitRef::from(qubit.clone());
        self.quadratic_coefficients
            .entry(key)
            .or_insert_with(HashMap::new);
    }

    fn insert_quadratic_coeff(&mut self, qubit1: &QubitRef, qubit2: &QubitRef, value: i32) {
        let key1 = HashableQubitRef::from(qubit1.clone());
        let key2 = HashableQubitRef::from(qubit2.clone());

        let hashmap: &mut HashMap<HashableQubitRef, i32> =
            self.quadratic_coefficients.get_mut(&key1).unwrap();

        if hashmap.contains_key(&key2) {
            let new_coeff = value + hashmap.get(&key2).unwrap();
            hashmap.insert(key2, new_coeff);
        } else {
            hashmap.insert(key2, value);
        }
    }

    pub fn add_quadratic_coeffs(&mut self, qubit1: &QubitRef, qubit2: &QubitRef, value: i32) {
        if value == 0 {
            return;
        } else if qubit1.as_ptr() == qubit2.as_ptr() {
            return self.add_linear_coeff(qubit1, value);
        }

        self.add_new_row(&qubit2);
        self.add_new_row(&qubit1);

        // trading space for time
        self.insert_quadratic_coeff(qubit1, qubit2, value);
        self.insert_quadratic_coeff(qubit2, qubit1, value);
    }

    pub fn add_offset(&mut self, value: i32) -> i32 {
        self.offset += value;
        self.offset
    }

    pub fn fix_variable(&mut self, qubit: &QubitRef, value: bool) {
        let num: i32 = (value as i32) as i32;

        let key = HashableQubitRef::from(qubit.clone());

        assert!(
            self.linear_coefficients.contains_key(&key)
                || self.quadratic_coefficients.contains_key(&key)
        );

        if self.linear_coefficients.contains_key(&key) {
            let coeff = self.linear_coefficients.get(&key).unwrap();
            self.offset += coeff * num;
            self.linear_coefficients.remove(&key);
        }

        if self.quadratic_coefficients.contains_key(&key) {
            let hashmap = <&HashMap<HashableQubitRef, i32>>::clone(
                &&self.quadratic_coefficients.get(&key).unwrap(),
            );
            let pairs: Vec<(QubitRef, i32)> =
                hashmap.iter().map(|(x, y)| (x.value.clone(), *y)).collect();
            for (qubit_ref, value) in pairs {
                self.add_linear_coeff(&qubit_ref, value * num);
                let key2 = HashableQubitRef::from(qubit_ref);
                self.quadratic_coefficients
                    .get_mut(&key2)
                    .unwrap()
                    .remove(&key);
            }
            self.quadratic_coefficients.remove(&key);
        }
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
    fn record_mapping(&mut self, gate: &GateRef, replacement: QubitRef) -> QubitRef {
        let key = HashableGateRef::from(gate.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement).unwrap()
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
                let z = QubitRef::from(Qubit {});
                self.qubo.add_linear_coeff(&operand, -2);
                self.qubo.add_linear_coeff(&z, -2);

                self.qubo.add_quadratic_coeffs(&operand, &z, 4);
                self.qubo.add_offset(2);
                self.record_mapping(&gate, z)
            }
            Gate::And { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, 0);
                self.qubo.add_linear_coeff(&x2, 0);
                self.qubo.add_linear_coeff(&z, 6);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2);
                self.qubo.add_quadratic_coeffs(&x1, &z, -4);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4);

                self.qubo.add_offset(0);
                self.record_mapping(&gate, z)
            }
            Gate::Nand { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, -4);
                self.qubo.add_linear_coeff(&x2, -4);
                self.qubo.add_linear_coeff(&z, -6);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2);
                self.qubo.add_quadratic_coeffs(&x1, &z, 4);
                self.qubo.add_quadratic_coeffs(&x2, &z, 4);

                self.qubo.add_offset(6);
                self.record_mapping(&gate, z)
            }
            Gate::Matriarch1 { cond, right } => {
                let x1 = self.visit(cond);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, 0);
                self.qubo.add_linear_coeff(&x2, 2);
                self.qubo.add_linear_coeff(&z, 2);

                self.qubo.add_quadratic_coeffs(&x1, &x2, -2);
                self.qubo.add_quadratic_coeffs(&x1, &z, 4);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4);

                self.qubo.add_offset(0);
                self.record_mapping(&gate, z)
            }
            Gate::Or { left, right } => {
                let x1 = self.visit(left);
                let x2 = self.visit(right);
                let z = QubitRef::from(Qubit {});

                self.qubo.add_linear_coeff(&x1, 2);
                self.qubo.add_linear_coeff(&x2, 2);
                self.qubo.add_linear_coeff(&z, 2);

                self.qubo.add_quadratic_coeffs(&x1, &x2, 2);
                self.qubo.add_quadratic_coeffs(&x1, &z, -4);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4);

                self.qubo.add_offset(0);
                self.record_mapping(&gate, z)
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let x1 = self.visit(input1);
                let x2 = self.visit(input2);

                let aux = QubitRef::from(Qubit {});
                let carry = QubitRef::from(Qubit {});
                let z = QubitRef::from(Qubit {});

                self.update_mapping_carries(gate, carry.clone());

                self.qubo.add_linear_coeff(&x1, 2);
                self.qubo.add_linear_coeff(&x2, 2);
                self.qubo.add_linear_coeff(&z, 2);
                self.qubo.add_linear_coeff(&aux, 4);
                self.qubo.add_linear_coeff(&carry, 4);

                self.qubo.add_quadratic_coeffs(&carry, &aux, 4);
                self.qubo.add_quadratic_coeffs(&x1, &aux, -4);
                self.qubo.add_quadratic_coeffs(&x1, &carry, -4);
                self.qubo.add_quadratic_coeffs(&x2, &aux, 4);
                self.qubo.add_quadratic_coeffs(&x2, &carry, -4);
                self.qubo.add_quadratic_coeffs(&x1, &x2, 0);
                self.qubo.add_quadratic_coeffs(&z, &aux, -4);
                self.qubo.add_quadratic_coeffs(&z, &carry, 4);
                self.qubo.add_quadratic_coeffs(&x1, &z, 0);
                self.qubo.add_quadratic_coeffs(&x2, &z, -4);

                self.qubo.add_offset(0);
                self.record_mapping(&gate, z)
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

                self.qubo.add_linear_coeff(&x1, 2);
                self.qubo.add_linear_coeff(&x2, 2);
                self.qubo.add_linear_coeff(&x3, 2);
                self.qubo.add_linear_coeff(&z, 2);
                self.qubo.add_linear_coeff(&aux, 4);
                self.qubo.add_linear_coeff(&carry, 4);

                self.qubo.add_quadratic_coeffs(&x1, &aux, -4);
                self.qubo.add_quadratic_coeffs(&x1, &carry, -4);
                self.qubo.add_quadratic_coeffs(&x2, &aux, -4);
                self.qubo.add_quadratic_coeffs(&x2, &carry, -4);
                self.qubo.add_quadratic_coeffs(&x1, &x2, 4);
                self.qubo.add_quadratic_coeffs(&x3, &aux, 4);
                self.qubo.add_quadratic_coeffs(&x3, &carry, -4);
                self.qubo.add_quadratic_coeffs(&z, &aux, -4);
                self.qubo.add_quadratic_coeffs(&z, &carry, 4);
                self.qubo.add_quadratic_coeffs(&z, &x3, -4);

                self.qubo.add_offset(0);
                self.record_mapping(&gate, z)
            }
            Gate::CarryHalfAdder { .. } => {
                let key = HashableGateRef::from(gate.clone());
                let gate_half_adder = self.bitblasting.mapping_adders.get(&key).unwrap();
                self.visit(gate_half_adder);

                let half_adder_key = HashableGateRef::from(gate_half_adder.clone());
                let z = (*self.mapping_carries.get(&half_adder_key).unwrap()).clone();
                self.record_mapping(&gate, z)
            }
            Gate::CarryFullAdder { .. } => {
                let key = HashableGateRef::from(gate.clone());
                let gate_full_adder = self.bitblasting.mapping_adders.get(&key).unwrap();
                self.visit(gate_full_adder);

                let full_adder_key = HashableGateRef::from(gate_full_adder.clone());
                let z = (*self.mapping_carries.get(&full_adder_key).unwrap()).clone();
                self.record_mapping(&gate, z)
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
                self.qubo.add_linear_coeff(&ored_bad_states, 2);
                self.qubo.add_linear_coeff(qubit, 2);
                self.qubo.add_linear_coeff(&z, 2);

                self.qubo.add_quadratic_coeffs(&ored_bad_states, qubit, 2);
                self.qubo.add_quadratic_coeffs(&ored_bad_states, &z, -4);
                self.qubo.add_quadratic_coeffs(qubit, &z, -4);
                ored_bad_states = z;
            }
        } else {
            panic!("No bad states qubits!");
        }

        // apply constraints
        for (gate, value) in self.bitblasting.constraints.iter() {
            let qubit = self.mapping.get(gate).unwrap();
            self.qubo.fix_variable(qubit, *value);
        }

        // fix true constants
        self.qubo.fix_variable(&self.const_true_qubit, true);

        // fix false constants
        self.qubo.fix_variable(&self.const_false_qubit, false);

        bad_state_qubits
    }

    fn evaluate_gate(
        &self,
        gate: &GateRef,
        fixed_values: &mut HashMap<HashableGateRef, bool>,
        offset: &mut i32,
    ) -> bool {
        let key = HashableGateRef::from(gate.clone());

        if let Some(result) = fixed_values.get(&key) {
            return *result;
        }

        match &*gate.borrow() {
            Gate::ConstTrue {} => true,
            Gate::ConstFalse {} => false,
            Gate::InputBit {} => {
                panic!("this case should not happend");
            }
            Gate::Not { value } => {
                let value = self.evaluate_gate(value, fixed_values, offset);
                let result = !value;

                *offset += (value as i32) * -2;
                *offset += (result as i32) * -2;
                *offset += (result as i32) * (value as i32) * 4;

                fixed_values.insert(key, result);
                result
            }
            Gate::And { left, right } => {
                let x1 = self.evaluate_gate(left, fixed_values, offset);
                let x2 = self.evaluate_gate(right, fixed_values, offset);
                let z = x1 && x2;

                *offset += (z as i32) * 6;

                *offset += (x1 as i32) * (x2 as i32) * 2;
                *offset += (x1 as i32) * (z as i32) * -4;
                *offset += (x2 as i32) * (z as i32) * -4;

                fixed_values.insert(key, z);
                z
            }
            Gate::Nand { left, right } => {
                let x1 = self.evaluate_gate(left, fixed_values, offset);
                let x2 = self.evaluate_gate(right, fixed_values, offset);
                let z = !(x1 && x2);

                *offset += (x1 as i32) * -4;
                *offset += (x2 as i32) * -4;
                *offset += (z as i32) * -6;

                *offset += (x1 as i32) * (x2 as i32) * 2;
                *offset += (x1 as i32) * (z as i32) * 4;
                *offset += (x2 as i32) * (z as i32) * 4;

                fixed_values.insert(key, z);
                z
            }
            Gate::Matriarch1 { cond, right } => {
                let x1 = self.evaluate_gate(cond, fixed_values, offset);
                let x2 = self.evaluate_gate(right, fixed_values, offset);
                let z = !x1 && x2;

                *offset += (x2 as i32) * 2;
                *offset += (z as i32) * 2;

                *offset += (x1 as i32) * (x2 as i32) * -2;
                *offset += (x1 as i32) * (z as i32) * 4;
                *offset += (x2 as i32) * (z as i32) * -4;

                fixed_values.insert(key, z);
                z
            }
            Gate::Or { left, right } => {
                let x1 = self.evaluate_gate(left, fixed_values, offset);
                let x2 = self.evaluate_gate(right, fixed_values, offset);
                let z = x1 || x2;

                *offset += (x1 as i32) * 2;
                *offset += (x2 as i32) * 2;
                *offset += (z as i32) * 2;

                *offset += (x1 as i32) * (x2 as i32) * 2;
                *offset += (x1 as i32) * (z as i32) * -4;
                *offset += (x2 as i32) * (z as i32) * -4;

                fixed_values.insert(key, z);
                z
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let x1 = self.evaluate_gate(input1, fixed_values, offset);
                let x2 = self.evaluate_gate(input2, fixed_values, offset);

                let carry = x1 && x2;
                let z = ((x1 as i32) + (x2 as i32) % 2) == 1;
                let aux = (x1 && !x2) as i32;

                *offset += (x1 as i32) * 2;
                *offset += (x2 as i32) * 2;
                *offset += (z as i32) * 2;
                *offset += (aux as i32) * 4;
                *offset += (carry as i32) * 4;

                *offset += (carry as i32) * aux * 4;
                *offset += (x1 as i32) * aux * -4;
                *offset += (x1 as i32) * (carry as i32) * -4;
                *offset += (x2 as i32) * aux * 4;
                *offset += (x2 as i32) * (carry as i32) * -4;
                *offset += (z as i32) * aux * -4;
                *offset += (z as i32) * (carry as i32) * 4;
                *offset += (x2 as i32) * (z as i32) * -4;

                let carry_key = self.bitblasting.mapping_adders.get(&key).unwrap().clone();
                fixed_values.insert(HashableGateRef::from(carry_key), carry);
                fixed_values.insert(key, z);

                z
            }
            Gate::ResultFullAdder {
                input1,
                input2,
                input3,
            } => {
                let x1 = self.evaluate_gate(input1, fixed_values, offset) as i32;
                let x2 = self.evaluate_gate(input2, fixed_values, offset) as i32;
                let x3 = self.evaluate_gate(input3, fixed_values, offset) as i32;

                let z = ((x1 + x2 + x3) % 2) == 1;
                let carry = (x1 + x2 + x3) > 1;

                // determine value of aux
                let aux: i32;

                if x1 == 0 {
                    if x2 == 0 {
                        aux = 0;
                    } else if x3 == 0 {
                        aux = 1;
                    } else {
                        aux = 0;
                    }
                } else if x2 == 1 {
                    aux = 1;
                } else if x3 == 1 {
                    aux = 0;
                } else {
                    aux = 1;
                }

                *offset += x1 * 2;
                *offset += x2 * 2;
                *offset += x3 * 2;
                *offset += (z as i32) * 2;
                *offset += aux * 4;
                *offset += (carry as i32) * 4;

                *offset += x1 * aux * -4;
                *offset += x1 * (carry as i32) * -4;
                *offset += x2 * aux * -4;
                *offset += x2 * (carry as i32) * -4;
                *offset += x1 * x2 * 4;
                *offset += x3 * aux * 4;
                *offset += x3 * (carry as i32) * -4;
                *offset += (z as i32) * aux * -4;
                *offset += (z as i32) * (carry as i32) * 4;
                *offset += x3 * (z as i32) * -4;

                let carry_key = self.bitblasting.mapping_adders.get(&key).unwrap().clone();
                fixed_values.insert(HashableGateRef::from(carry_key), carry as bool);
                fixed_values.insert(key, z);

                z
            }
            Gate::CarryHalfAdder { .. } => {
                let gate_half_adder = self.bitblasting.mapping_adders.get(&key).unwrap();
                self.evaluate_gate(gate_half_adder, fixed_values, offset);

                *(fixed_values.get(&key).unwrap())
            }
            Gate::CarryFullAdder { .. } => {
                let gate_full_adder = self.bitblasting.mapping_adders.get(&key).unwrap();
                self.evaluate_gate(gate_full_adder, fixed_values, offset);

                *(fixed_values.get(&key).unwrap())
            }
        }
    }

    fn add_const_to_fixed_values(
        &self,
        fixed_values: &mut HashMap<HashableGateRef, bool>,
        gates: &[GateRef],
        mut value: i64,
    ) {
        for gate in gates {
            let key = HashableGateRef::from((*gate).clone());
            assert!(!fixed_values.contains_key(&key));

            fixed_values.insert(key, value % 2 == 1);
            value /= 2;
        }
    }

    pub fn evaluate_inputs(
        &mut self,
        bad_state_gates: &[GateRef],
        input_values: &[i64],
    ) -> (i32, Vec<NodeRef>) {
        // the order of inputs values has to be the same as BitBlasting::input_gates

        let mut true_bad_nids: Vec<NodeRef> = Vec::new();

        let mut fixed_values: HashMap<HashableGateRef, bool> = HashMap::new();

        for ((_, gates), value) in self.bitblasting.input_gates.iter().zip(input_values.iter()) {
            self.add_const_to_fixed_values(&mut fixed_values, gates, *value);
        }

        let mut offset: i32 = self.qubo.offset;

        for gate in bad_state_gates {
            if self.evaluate_gate(gate, &mut fixed_values, &mut offset) {
                let key = HashableGateRef::from(gate.clone());
                true_bad_nids.push(
                    self.bitblasting
                        .gates_to_bad_nids
                        .get(&key)
                        .unwrap()
                        .clone(),
                );
            }
        }

        (offset, true_bad_nids)
    }
}

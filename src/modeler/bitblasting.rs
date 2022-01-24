use crate::modeler::{get_bitsize, HashableNodeRef, Model, Node, NodeRef, NodeType};
use std::collections::HashMap;
use std::rc::Rc;

// public interface

pub fn bitblast_model(model: &Model, constant_propagation: bool) -> Vec<GateRef> {
    let mut bitblasting = BitBlasting::new(constant_propagation);

    bitblasting.process_model(model)
}
type GateRef = Rc<Gate>;

#[derive(PartialEq, Eq)]
pub enum Gate {
    ConstTrue,
    ConstFalse,
    InputBit,
    Not {
        value: GateRef,
    },
    And {
        left: GateRef,
        right: GateRef,
    },
    Nand {
        left: GateRef,
        right: GateRef,
    },
    Or {
        left: GateRef,
        right: GateRef,
    },
    Matriarch1 {
        left: GateRef,
        right: GateRef,
    },
    // Matriarch2  {
    //     left: GateRef,
    //     right: GateRef,
    // },
    CarryHalfAdder {
        left: GateRef,
        right: GateRef,
    },
    ResultHalfAdder {
        input1: GateRef,
        input2: GateRef,
    },
    CarryFullAdder {
        input1: GateRef,
        input2: GateRef,
        input3: GateRef,
    },
    ResultFullAdder {
        input1: GateRef,
        input2: GateRef,
        input3: GateRef,
    },
}

// struct HashableGateRef {
//     value: GateRef
// }

fn get_gate_from_constant_bit(bit: u64) -> GateRef {
    assert!((bit == 0) | (bit == 1));
    if bit == 1 {
        GateRef::from(Gate::ConstTrue)
    } else {
        GateRef::from(Gate::ConstFalse)
    }
}

fn is_constant(gate_type: GateRef) -> bool {
    *gate_type == Gate::ConstFalse || *gate_type == Gate::ConstTrue
}

fn get_constant(gate_type: GateRef) -> Option<bool> {
    if is_constant(gate_type.clone()) {
        if *gate_type == Gate::ConstFalse {
            Some(false)
        } else {
            Some(true)
        }
    } else {
        None
    }
}

fn get_2s_complement(bitvector: Vec<GateRef>) -> Vec<GateRef> {
    // invert bits

    let mut inverted_bits: Vec<GateRef> = Vec::new();

    for bit in bitvector {
        inverted_bits.push(not_gate(bit));
    }

    // build a bitvector that represents 1

    let mut bitvector_1: Vec<GateRef> = vec![GateRef::from(Gate::ConstTrue)];

    assert!(bitvector_1.len() < inverted_bits.len());
    while bitvector_1.len() != inverted_bits.len() {
        bitvector_1.push(GateRef::from(Gate::ConstFalse));
    }

    bitwise_add(inverted_bits, bitvector_1)
}

// fn get_numeric_from_gate(gate_type: GateRef) -> Option<u8> {
//     if let Some(result) = get_constant(gate_type) {
//         if result {
//             Some(1)
//         } else {
//             Some(0)
//         }
//     } else {
//         None
//     }
// }

fn get_gate_from_boolean(a: bool) -> GateRef {
    if a {
        GateRef::from(Gate::ConstTrue)
    } else {
        GateRef::from(Gate::ConstFalse)
    }
}

fn are_there_false_constants(const1: Option<bool>, const2: Option<bool>) -> bool {
    if let Some(a) = const1 {
        if !a {
            return true;
        }
    }

    if let Some(b) = const2 {
        return !b;
    }
    false
}

fn are_there_true_constants(const1: Option<bool>, const2: Option<bool>) -> bool {
    if let Some(a) = const1 {
        if a {
            return true;
        }
    }

    if let Some(b) = const2 {
        return b;
    }
    false
}

fn are_both_constants(const1: Option<bool>, const2: Option<bool>) -> bool {
    if let Some(_a) = const1 {
        if let Some(_b) = const2 {
            return true;
        }
    }
    false
}

fn get_non_constant_gate(gates: Vec<GateRef>) -> Option<GateRef> {
    for gate in gates {
        if let Some(_g) = get_constant(gate.clone()) {
            return Some(gate);
        }
    }
    None
}

fn get_replacement_from_constant(sort: &NodeType, value_: u64) -> Vec<GateRef> {
    let total_bits = get_bitsize(sort);
    let mut replacement: Vec<GateRef> = Vec::new();
    let mut value = value_;
    for _ in 0..total_bits {
        replacement.push(get_gate_from_constant_bit(value % 2));
        value /= 2;
    }
    replacement
}

fn get_replacement_from_unique_gate(sort: &NodeType, gate_type: Gate) -> Vec<GateRef> {
    let total_bits = get_bitsize(sort);
    let mut replacement: Vec<GateRef> = Vec::new();
    let gate = GateRef::from(gate_type);
    for _ in 0..total_bits {
        replacement.push(gate.clone());
    }
    replacement
}

fn and_gate(a: Option<bool>, b: Option<bool>, a_gate: GateRef, b_gate: GateRef) -> GateRef {
    if are_both_constants(a, b) {
        get_gate_from_boolean(a.unwrap() && b.unwrap())
    } else if are_there_false_constants(a, b) {
        GateRef::from(Gate::ConstFalse)
    } else if let Some(result) = get_non_constant_gate(vec![a_gate.clone(), b_gate.clone()]) {
        result
    } else {
        GateRef::from(Gate::And {
            left: a_gate,
            right: b_gate,
        })
    }
}

fn or_gate(a: Option<bool>, b: Option<bool>, a_gate: GateRef, b_gate: GateRef) -> GateRef {
    if are_both_constants(a, b) {
        get_gate_from_boolean(a.unwrap() || b.unwrap())
    } else if are_there_true_constants(a, b) {
        GateRef::from(Gate::ConstTrue)
    } else if are_there_false_constants(a, b) {
        get_non_constant_gate(vec![a_gate, b_gate]).unwrap()
    } else {
        GateRef::from(Gate::Or {
            left: a_gate,
            right: b_gate,
        })
    }
}

fn not_gate(a_gate: GateRef) -> GateRef {
    let a = get_constant(a_gate.clone());

    if let Some(a_const) = a {
        if a_const {
            GateRef::from(Gate::ConstFalse)
        } else {
            GateRef::from(Gate::ConstTrue)
        }
    } else {
        GateRef::from(Gate::Not { value: a_gate })
    }
}

fn xnor_gate(a: Option<bool>, b: Option<bool>, a_gate: GateRef, b_gate: GateRef) -> GateRef {
    if are_both_constants(a, b) {
        get_gate_from_boolean(a.unwrap() == b.unwrap())
    } else if are_there_false_constants(a, b) {
        let non_constant = get_non_constant_gate(vec![a_gate, b_gate]).unwrap();
        GateRef::from(Gate::Not {
            value: non_constant,
        })
    } else if let Some(result) = get_non_constant_gate(vec![a_gate.clone(), b_gate.clone()]) {
        result
    } else {
        let not_a = GateRef::from(Gate::Not {
            value: a_gate.clone(),
        });
        let not_b = GateRef::from(Gate::Not {
            value: b_gate.clone(),
        });

        let nand1 = GateRef::from(Gate::Nand {
            left: a_gate,
            right: b_gate,
        });
        let nand2 = GateRef::from(Gate::Nand {
            left: not_a,
            right: not_b,
        });

        GateRef::from(Gate::Nand {
            left: nand1,
            right: nand2,
        })
    }
}

fn bitwise_add(left: Vec<GateRef>, right: Vec<GateRef>) -> Vec<GateRef> {
    fn are_there_2_constants(bit1: GateRef, bit2: GateRef, bit3: GateRef) -> bool {
        let const1 = get_constant(bit1).unwrap_or(false) as u8;
        let const2 = get_constant(bit2).unwrap_or(false) as u8;
        let const3 = get_constant(bit3).unwrap_or(false) as u8;
        (const1 + const2 + const3) == 2
    }

    fn get_2_constants(bit1: Option<bool>, bit2: Option<bool>, bit3: Option<bool>) -> (bool, bool) {
        if let Some(const1) = bit1 {
            if let Some(const2) = bit2 {
                (const1, const2)
            } else if let Some(const3) = bit3 {
                (const1, const3)
            } else {
                panic!("Expecting 2 constants")
            }
        } else if let Some(const2) = bit2 {
            if let Some(const3) = bit3 {
                (const2, const3)
            } else {
                panic!("Expecting 2 constants")
            }
        } else {
            panic!("Expecting 2 constants")
        }
    }

    assert!(left.len() == right.len());
    let mut replacement: Vec<GateRef> = Vec::new();
    let mut carry: GateRef = GateRef::from(Gate::ConstFalse); // initlaize so compiler not complains
    let mut is_first = true;
    for (l_bit, r_bit) in left.iter().zip(right.iter()) {
        let l_const = get_constant(l_bit.clone());
        let r_const = get_constant(r_bit.clone());
        if is_first {
            // half adders
            if are_both_constants(l_const, r_const) {
                carry = get_gate_from_boolean(l_const.unwrap() && r_const.unwrap());
                replacement.push(get_gate_from_boolean(l_const.unwrap() != r_const.unwrap()));
            } else if are_there_false_constants(l_const, r_const) {
                carry = GateRef::from(Gate::ConstFalse);
                let non_constant =
                    get_non_constant_gate(vec![l_bit.clone(), r_bit.clone()]).unwrap();
                replacement.push(non_constant);
            } else if are_there_true_constants(l_const, r_const) {
                let non_constant =
                    get_non_constant_gate(vec![l_bit.clone(), r_bit.clone()]).unwrap();
                carry = non_constant.clone();
                replacement.push(GateRef::from(Gate::Not {
                    value: non_constant,
                }));
            } else {
                carry = GateRef::from(Gate::CarryHalfAdder {
                    left: (*l_bit).clone(),
                    right: (*r_bit).clone(),
                });
                replacement.push(GateRef::from(Gate::ResultHalfAdder {
                    input1: (*l_bit).clone(),
                    input2: (*r_bit).clone(),
                }));
            }
            is_first = false;
        // Full adders
        } else if are_both_constants(l_const, r_const) && is_constant(carry.clone()) {
            let carry_const = get_constant(carry.clone());
            let result = ((l_const.unwrap() as u64)
                + (r_const.unwrap() as u64)
                + (carry_const.unwrap() as u64))
                % 2;

            replacement.push(get_gate_from_constant_bit(result));

            let temp = ((l_const.unwrap() as u8)
                + (r_const.unwrap() as u8)
                + (carry_const.unwrap() as u8))
                > 1;
            carry = get_gate_from_boolean(temp);
        } else if are_there_2_constants((*l_bit).clone(), (*r_bit).clone(), carry.clone()) {
            let carry_const = get_constant(carry.clone());
            let (const1, const2) = get_2_constants(l_const, r_const, carry_const);
            if let Some(non_const) =
                get_non_constant_gate(vec![(*l_bit).clone(), (*r_bit).clone(), carry.clone()])
            {
                if const1 && const2 {
                    carry = GateRef::from(Gate::ConstTrue);
                    replacement.push(non_const);
                } else if const1 != const2 {
                    carry = non_const.clone();
                    replacement.push(GateRef::from(Gate::Not { value: non_const }));
                } else {
                    carry = GateRef::from(Gate::ConstFalse);
                    replacement.push(non_const);
                }
            } else {
                panic!("bug in building addition circuit")
            }
        } else {
            // no constant propagation is possible
            replacement.push(GateRef::from(Gate::ResultFullAdder {
                input1: (*l_bit).clone(),
                input2: (*r_bit).clone(),
                input3: carry.clone(),
            }));

            carry = GateRef::from(Gate::CarryFullAdder {
                input1: (*l_bit).clone(),
                input2: (*r_bit).clone(),
                input3: carry.clone(),
            });
        }
    }

    replacement
}

pub struct BitBlasting {
    mapping: HashMap<HashableNodeRef, Vec<GateRef>>,
    constant_propagation: bool,
    // computed_values: HashMap<GateRef, bool>
}

impl BitBlasting {
    pub fn new(constant_propagation_: bool) -> Self {
        Self {
            mapping: HashMap::new(),
            constant_propagation: constant_propagation_,
            // computed_values: HashMap::new()
        }
    }

    fn record_mapping(&mut self, node: &NodeRef, replacement: Vec<GateRef>) -> Vec<GateRef> {
        let key = HashableNodeRef::from(node.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement).unwrap()
    }

    fn query_existence(&mut self, node: &NodeRef) -> Option<Vec<GateRef>> {
        let key = HashableNodeRef::from(node.clone());
        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned()
        } else {
            None
        }
    }

    fn fold_bitwise_gate<F>(
        &mut self,
        left: Vec<GateRef>,
        right: Vec<GateRef>,
        f_gate: F,
        _f_name: &str,
    ) -> Vec<GateRef>
    where
        F: Fn(Option<bool>, Option<bool>, GateRef, GateRef) -> GateRef,
    {
        assert!(left.len() == right.len());

        let mut replacement: Vec<GateRef> = Vec::new();

        for (l_bit, r_bit) in left.iter().zip(right.iter()) {
            if self.constant_propagation {
                let l_bit_const = get_constant(l_bit.clone());
                let r_bit_const = get_constant(r_bit.clone());
                replacement.push(f_gate(
                    l_bit_const,
                    r_bit_const,
                    (*l_bit).clone(),
                    (*r_bit).clone(),
                ));
            } else {
                replacement.push(GateRef::from(Gate::And {
                    left: (*l_bit).clone(),
                    right: (*r_bit).clone(),
                }))
            }
        }
        replacement
    }

    fn fold_word_gate<F>(&mut self, word: Vec<GateRef>, f_gate: F, _f_name: &str) -> Vec<GateRef>
    where
        F: Fn(Option<bool>, Option<bool>, GateRef, GateRef) -> GateRef,
    {
        assert!(!word.is_empty());

        let mut current = word[0].clone();
        for w in word.iter().skip(1) {
            let a = get_constant(current.clone());
            let b = get_constant((*w).clone());
            current = f_gate(a, b, current, (*w).clone());
        }

        vec![current]
    }

    fn visit(&mut self, node: &NodeRef) -> Vec<GateRef> {
        let key = HashableNodeRef::from(node.clone());
        if self.mapping.contains_key(&key) {
            self.mapping.get(&key).cloned().unwrap()
        } else {
            let replacement = self.process(node);
            assert!(!self.mapping.contains_key(&key));
            replacement
        }
    }

    fn process(&mut self, node: &NodeRef) -> Vec<GateRef> {
        match &*node.borrow() {
            Node::Const { nid: _, sort, imm } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let replacement = get_replacement_from_constant(sort, *imm);
                    self.record_mapping(node, replacement)
                }
            } Node::Input { nid: _, sort, name: _ } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let replacement = get_replacement_from_unique_gate(sort, Gate::InputBit);
                    self.record_mapping(node, replacement)
                }

            } Node::State { nid: _, sort, init, name: _ } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                }else {
                    let replacement;
                    if let Some(value) = init {
                        replacement = self.visit(value);
                    } else {
                        replacement = get_replacement_from_unique_gate(sort, Gate::ConstFalse);
                    }
                    self.record_mapping(node, replacement)
                }
            }  Node::Not { nid: _, value } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let bitvector = self.visit(value);
                    let mut replacement: Vec<GateRef> = Vec::new();
                    for bit in bitvector {
                        replacement.push(not_gate(bit));
                    }
                    self.record_mapping(node, replacement)
                }
            }  Node::Bad { nid: _, cond, name: _ } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let replacement = self.visit(cond);
                    self.record_mapping(node, replacement)
                }
            } Node::And { nid: _, left, right } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let left_operand = self.visit(left);
                    let right_operand = self.visit(right);
                    let replacement = self.fold_bitwise_gate(left_operand, right_operand, and_gate, "AND");
                    self.record_mapping(node, replacement)
                }
            } Node::Ext { nid: _, from, value } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let mut replacement: Vec<GateRef> = self.visit(value);
                    while replacement.len() < get_bitsize(from) {
                        replacement.push(GateRef::from(Gate::ConstFalse));
                    }
                    self.record_mapping(node, replacement)
                }
            } Node::Eq { nid: _, left, right } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let left_operand = self.visit(left);
                    let right_operand = self.visit(right);
                    let temp_word = self.fold_bitwise_gate(left_operand, right_operand, xnor_gate, "XNOR");
                    let replacement = self.fold_word_gate(temp_word, and_gate, "WORD-AND");
                    self.record_mapping(node, replacement)
                }
            } Node::Add { nid: _, left, right } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let left_operand = self.visit(left);
                    let right_operand = self.visit(right);
                    let replacement = bitwise_add(left_operand, right_operand);
                    self.record_mapping(node, replacement)
                }
            } Node::Ite {nid: _, sort: _, cond, left, right} => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let cond_operand = self.visit(cond);
                    assert!(cond_operand.len() == 1);
                    if let Some(cond_const) = get_constant(cond_operand[0].clone()) {
                        if cond_const {
                            let left_operand = self.visit(left);
                            self.record_mapping(node,  left_operand)
                        } else{
                            let right_operand = self.visit(right);
                            self.record_mapping(node, right_operand)
                        }
                    } else {
                        let left_operand = self.visit(left);
                        let right_operand = self.visit(right);
                        assert!(left_operand.len() == right_operand.len());

                        let mut replacement: Vec<GateRef> = Vec::new();
                        for i in 0..left_operand.len() {
                            let left_bit = get_constant(left_operand[i].clone());
                            let right_bit = get_constant(right_operand[i].clone());

                            if are_both_constants(left_bit, right_bit) {
                                let const_true_bit = get_constant(left_operand[i].clone()).unwrap();
                                let const_false_bit = get_constant(right_operand[i].clone()).unwrap();

                                if const_true_bit == const_false_bit {
                                    replacement.push(left_operand[i].clone());
                                } else if const_true_bit {
                                    replacement.push(cond_operand[0].clone())
                                } else {
                                    replacement.push(GateRef::from(Gate::Not{value: cond_operand[0].clone()}))
                                }
                            } else {
                                let true_bit: GateRef;
                                let false_bit: GateRef;

                                if let Some(const_true) = get_constant(left_operand[i].clone()) {
                                    if const_true {
                                        true_bit = cond_operand[0].clone();
                                    } else {
                                        true_bit = GateRef::from(Gate::Not{value: cond_operand[0].clone()});
                                     }
                                } else {
                                    true_bit = GateRef::from(Gate::And{left: left_operand[i].clone(), right: cond_operand[0].clone()});
                                }

                                if let Some(const_false) = get_constant(right_operand[i].clone()) {
                                    if const_false {
                                        false_bit = GateRef::from(Gate::Not{value: cond_operand[0].clone()});
                                    } else {
                                        false_bit = GateRef::from(Gate::ConstFalse);
                                    }
                                } else {
                                    false_bit = GateRef::from(Gate::Matriarch1{left: cond_operand[0].clone(), right: right_operand[i].clone()});
                                }

                                let true_bit_const = get_constant(true_bit.clone());
                                let false_bit_const = get_constant(false_bit.clone());
                                replacement.push(or_gate(true_bit_const, false_bit_const, true_bit, false_bit));
                            }


                        }
                        self.record_mapping(node, replacement)
                    }
                }
            } Node::Sub { nid: _, left, right } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let mut left_operand = self.visit(left);
                    let mut right_operand = self.visit(right);

                    left_operand.push(GateRef::from(Gate::ConstFalse));
                    right_operand.push(GateRef::from(Gate::ConstFalse));

                    right_operand = get_2s_complement(right_operand);

                    let replacement: Vec<GateRef> = bitwise_add(left_operand, right_operand);
                    self.record_mapping(node, replacement)
                }
            }
            _ => {
                let replacement: Vec<GateRef> = Vec::new();
                replacement
            } // } Node::Read { nid, memory, address } =>
              //     //buffer.write_all(format!("{} read 2 {} {}\n", nid, get_nid(memory), get_nid(address)).as_bytes())?,
              // Node::Write { nid, memory, address, value } =>
              //     //buffer.write_all(format!("{} write 3 {} {} {}\n", nid, get_nid(memory), get_nid(address), get_nid(value)).as_bytes())?,
              // Node::Mul {nid, left, right} =>
              //     //buffer.write_all(format!("{} mul 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Div { nid, left, right } =>
              //     //buffer.write_all(format!("{} udiv 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Rem { nid, left, right } =>
              //     //buffer.write_all(format!("{} urem 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Ult { nid, left, right } =>
              //     //buffer.write_all(format!("{} ult 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
        }
    }

    pub fn process_model(&mut self, model: &Model) -> Vec<GateRef> {
        // returns bad state bits
        let mut bad_state_gates: Vec<GateRef> = Vec::new();
        for node in &model.bad_states_initial {
            let bitblasted_bad_state = self.process(node);
            assert!(bitblasted_bad_state.len() == 1);
            bad_state_gates.push(bitblasted_bad_state[0].clone());
        }
        bad_state_gates
    }
}

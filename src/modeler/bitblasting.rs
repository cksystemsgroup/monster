use crate::modeler::{get_bitsize, HashableNodeRef, Model, Node, NodeRef, NodeType};
use std::collections::HashMap;
use std::rc::Rc;

// public interface

pub fn bitblast_model(model: &Model) -> Vec<GateRef> {
    let mut bitblasting = BitBlasting::new();
    bitblasting.process_model(model)
}
type GateRef = Rc<Gate>;

#[derive(PartialEq, Eq)]
pub enum Gate {
    ConstTrue,
    ConstFalse,
    InputBit,
    Not { value: GateRef },
    And { left: GateRef, right: GateRef },
    // Bad {
    //     cond: GateRef,
    // },

    // Nand {
    //     left: GateRef,
    //     right: GateRef,
    // },
    // Or {
    //     left: GateRef,
    //     right: GateRef,
    // },
    // Xnor {
    //     left: GateRef,
    //     right: GateRef,
    // },
    // Xor {
    //     left: GateRef,
    //     right: GateRef,
    // },
    // Matriarch1 {
    //     left: GateRef,
    //     right: GateRef,
    // },
    // Matriarch2  {
    //     left: GateRef,
    //     right: GateRef,
    // },
    // AuxFullAdder, CarryFullAdder, ResultFullAdder {
    //     input1: GateRef,
    //     input2: GateRef,
    //     input3: GateRef
    // }
}

// struct HashableGateRef {
//     value: GateRef
// }

pub struct BitBlasting {
    mapping: HashMap<HashableNodeRef, Vec<GateRef>>,
    // computed_values: HashMap<GateRef, bool>
}

impl BitBlasting {
    pub fn new() -> Self {
        Self {
            mapping: HashMap::new(),
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

    fn get_gate_from_constant_bit(&mut self, bit: u64) -> GateRef {
        assert!((bit == 0) | (bit == 1));
        if bit == 1 {
            GateRef::from(Gate::ConstTrue)
        } else {
            GateRef::from(Gate::ConstFalse)
        }
    }

    fn get_replacement_from_constant(&mut self, sort: &NodeType, value_: u64) -> Vec<GateRef> {
        let total_bits = get_bitsize(sort);
        let mut replacement: Vec<GateRef> = Vec::new();
        let mut value = value_;
        for _ in 0..total_bits {
            replacement.push(self.get_gate_from_constant_bit(value % 2));
            value /= 2;
        }
        replacement
    }

    fn get_replacement_from_unique_gate(
        &mut self,
        sort: &NodeType,
        gate_type: Gate,
    ) -> Vec<GateRef> {
        let total_bits = get_bitsize(sort);
        let mut replacement: Vec<GateRef> = Vec::new();
        let gate = GateRef::from(gate_type);
        for _ in 0..total_bits {
            replacement.push(gate.clone());
        }
        replacement
    }

    fn is_constant(&mut self, gate_type: GateRef) -> bool {
        *gate_type == Gate::ConstFalse || *gate_type == Gate::ConstTrue
    }

    fn get_constant(&mut self, gate_type: GateRef) -> Option<bool> {
        if self.is_constant(gate_type.clone()) {
            if *gate_type == Gate::ConstFalse {
                Some(false)
            } else {
                Some(true)
            }
        } else {
            None
        }
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
                    let replacement = self.get_replacement_from_constant(sort, *imm);
                    self.record_mapping(node, replacement)
                }
            } Node::Input { nid: _, sort, name: _ } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let replacement = self.get_replacement_from_unique_gate(sort, Gate::InputBit);
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
                        replacement = self.get_replacement_from_unique_gate(sort, Gate::ConstFalse);
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
                        if self.is_constant(bit.clone()) {
                            if *bit == Gate::ConstFalse {
                                replacement.push(GateRef::from(Gate::ConstTrue));
                            } else {
                                assert!(*bit == Gate::ConstTrue);
                                replacement.push(GateRef::from(Gate::ConstFalse));
                            }
                        } else {
                            replacement.push(GateRef::from(Gate::Not{value:bit}))
                        }
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
                    assert!(left_operand.len() == right_operand.len());

                    let mut replacement: Vec<GateRef> = Vec::new();
                    for (l_bit, r_bit) in left_operand.iter().zip(right_operand.iter()) {
                        if let Some(l_bit_const) = self.get_constant(l_bit.clone()) {
                            if let Some(r_bit_const) = self.get_constant(r_bit.clone()) {
                                if l_bit_const && r_bit_const {
                                    replacement.push(GateRef::from(Gate::ConstTrue));
                                } else {
                                    replacement.push(GateRef::from(Gate::ConstFalse));
                                }
                            } else if l_bit_const {
                                replacement.push((*r_bit).clone());
                            } else {
                                replacement.push(GateRef::from(Gate::ConstFalse));
                            }
                        } else if let Some(r_bit_const) = self.get_constant(r_bit.clone()) {
                            if r_bit_const {
                                replacement.push((*l_bit).clone());
                            } else {
                                replacement.push(GateRef::from(Gate::ConstFalse));
                            }
                        } else {
                            replacement.push(GateRef::from(Gate::And{left:(*l_bit).clone(), right:(*r_bit).clone()}));
                        }
                    }
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
            }
            _ => {
                let replacement: Vec<GateRef> = Vec::new();
                replacement
            } // } Node::Read { nid, memory, address } =>
              //     //buffer.write_all(format!("{} read 2 {} {}\n", nid, get_nid(memory), get_nid(address)).as_bytes())?,
              // Node::Write { nid, memory, address, value } =>
              //     //buffer.write_all(format!("{} write 3 {} {} {}\n", nid, get_nid(memory), get_nid(address), get_nid(value)).as_bytes())?,
              // Node::Add { nid, left, right } =>
              //     //buffer.write_all(format!("{} add 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Sub { nid, left, right } =>
              //     //buffer.write_all(format!("{} sub 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Mul {nid, left, right} =>
              //     //buffer.write_all(format!("{} mul 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Div { nid, left, right } =>
              //     //buffer.write_all(format!("{} udiv 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Rem { nid, left, right } =>
              //     //buffer.write_all(format!("{} urem 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Ult { nid, left, right } =>
              //     //buffer.write_all(format!("{} ult 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Ite { nid, sort, cond, left, right } =>
              //     buffer.write_all(format!("{} ite {} {} {} {}\n", nid, get_sort(sort), get_nid(cond), get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Eq { nid, left, right } =>
              //     buffer.write_all(format!("{} eq 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
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

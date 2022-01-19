use crate::modeler::{get_bitsize, HashableNodeRef, Model, Node, NodeRef};
use std::collections::HashMap;
use std::rc::Rc;

// public interface

pub fn bitblast_model(model: &Model) -> Vec<GateRef> {
    let mut bitblasting = BitBlasting::new();
    bitblasting.process_model(model)
}
type GateRef = Rc<Gate>;

pub enum Gate {
    ConstTrue,
    ConstFalse,
    // InputBit,
    // Not{
    //     value: GateRef,
    // },
    // Bad {
    //     cond: GateRef,
    // },
    // And {
    //     left: GateRef,
    //     right: GateRef,
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

    fn record_mapping(&mut self, node: &NodeRef, replacement: Vec<GateRef>) {
        let key = HashableNodeRef::from(node.clone());
        assert!(!self.mapping.contains_key(&key));
        self.mapping.insert(key, replacement);
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

    fn process(&mut self, node: &NodeRef) -> Vec<GateRef> {
        match &*node.borrow() {
            Node::Const { nid: _, sort, imm } => {
                if let Some(replacement) = self.query_existence(node) {
                    replacement
                } else {
                    let total_bits = get_bitsize(sort);
                    let mut replacement: Vec<GateRef> = Vec::new();
                    let mut value = *imm;
                    for _ in 0..(total_bits) {
                        replacement.push(self.get_gate_from_constant_bit(value % 2));
                        value /= 2;
                    }
                    self.record_mapping(node, replacement);
                    self.query_existence(node).unwrap()
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
              // Node::Ext { nid, from, value } =>
              //     //buffer.write_all(format!("{} uext 2 {} {}\n", nid, get_nid(value), 64 - get_bitsize(from)).as_bytes())?,
              // Node::Ite { nid, sort, cond, left, right } =>
              //     buffer.write_all(format!("{} ite {} {} {} {}\n", nid, get_sort(sort), get_nid(cond), get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Eq { nid, left, right } =>
              //     buffer.write_all(format!("{} eq 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::And { nid, left, right } =>
              //     buffer.write_all(format!("{} and 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
              // Node::Not { nid, value } =>
              //     buffer.write_all(format!("{} not 1 {}\n", nid, get_nid(value)).as_bytes())?,
              // Node::State { nid, sort, init, name } => {
              //     buffer.write_all(format!("{} state {} {}\n", nid, get_sort(sort), name.as_deref().unwrap_or("?")).as_bytes())?;
              //     if let Some(value) = init {
              //         buffer.write_all(format!("{} init {} {} {}\n", nid + 1, get_sort(sort), nid, get_nid(value)).as_bytes())?;
              //     }
              // }
              // Node::Next { nid, sort, state, next } =>
              //     buffer.write_all(format!("{} next {} {} {}\n", nid, get_sort(sort), get_nid(state), get_nid(next)).as_bytes())?,
              // Node::Input { nid, sort, name } =>
              //     buffer.write_all(format!("{} input {} {}\n", nid, get_sort(sort), name).as_bytes())?,
              // Node::Bad { nid, cond, name } =>
              //     buffer.write_all(format!("{} bad {} {}\n", nid, get_nid(cond), name.as_deref().unwrap_or("?")).as_bytes())?
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

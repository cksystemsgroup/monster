use crate::modeler::bitblasting::{Gate, GateRef, HashableGateRef};
use crate::modeler::{Model, Nid, Node};
use log::info;
use std::collections::HashMap;

//
// Public Interface
//

pub fn print_gate_model(model: &Model, bad_state_gates: &[GateRef]) {
    let zip = model.bad_states_initial.iter().zip(bad_state_gates.iter());
    let mut printer = GateModelPrinter::new();
    println!("1 sort bitvec 1 ; Gates");
    for (bad_state, gate) in zip {
        if let Node::Bad { name, .. } = &*bad_state.borrow() {
            info!("NOW: {}", name.as_deref().unwrap_or("?"));
            let bad_condition_nid = printer.visit(gate);
            // XXX Move this into the printer, because it needs to bump self.current_nid!!!
            println!(
                "{} bad {} {}",
                bad_condition_nid + 1,
                bad_condition_nid,
                name.as_deref().unwrap_or("?")
            );
        } else {
            panic!("expecting 'Bad' node here");
        }
    }
}

//
// Private Implementation
//

struct GateModelPrinter {
    current_nid: Nid,
    nid_mapping: HashMap<HashableGateRef, Nid>,
}

impl GateModelPrinter {
    fn new() -> Self {
        Self {
            current_nid: 70000000,
            nid_mapping: HashMap::new(),
        }
    }

    fn next_nid(&mut self) -> Nid {
        let nid = self.current_nid;
        self.current_nid += 1;
        nid
    }

    fn visit(&mut self, gate: &GateRef) -> Nid {
        let key = HashableGateRef::from(gate.clone());
        self.nid_mapping.get(&key).copied().unwrap_or_else(|| {
            let assigned_nid = self.process(gate);
            assert!(!self.nid_mapping.contains_key(&key));
            self.nid_mapping.insert(key, assigned_nid);
            assigned_nid
        })
    }

    #[rustfmt::skip]
    fn process(&mut self, gate: &GateRef) -> Nid {
        match &*gate.borrow() {
            Gate::ConstTrue => {
                let gate_nid = self.next_nid();
                println!("{} constd 1 1", gate_nid);
                gate_nid
            }
            Gate::ConstFalse => {
                let gate_nid = self.next_nid();
                println!("{} constd 1 0", gate_nid);
                gate_nid
            }
            Gate::InputBit => {
                let gate_nid = self.next_nid();
                // TODO: We need a sensible name on the Gate::InputBit struct.
                println!("{} state 1 needs-a-name[{}]", gate_nid, gate_nid);
                gate_nid
            }
            Gate::Not { value } => {
                let value_nid = self.visit(value);
                let gate_nid = self.next_nid();
                println!("{} not 1 {}", gate_nid, value_nid);
                gate_nid
            }
            Gate::And { left, right } => {
                let left_nid = self.visit(left);
                let right_nid = self.visit(right);
                let gate_nid = self.next_nid();
                println!("{} and 1 {} {}", gate_nid, left_nid, right_nid);
                gate_nid
            }
            Gate::Nand { left: _, right: _ } => {
                panic!("implement Gate::Nand")
            }
            Gate::Or { left: _, right: _ } => {
                panic!("implement Gate::Or")
            }
            Gate::Matriarch1 { cond: _, right: _ } => {
                panic!("implement Gate::Matriarch1")
            }
            Gate::CarryHalfAdder { left, right } => {
                let left_nid = self.visit(left);
                let right_nid = self.visit(right);
                let gate_nid = self.next_nid();
                // Modeling as `C := and(A, B)` here:
                println!("{} and 1 {} {}", gate_nid, left_nid, right_nid);
                gate_nid
            }
            Gate::ResultHalfAdder { input1, input2 } => {
                let input1_nid = self.visit(input1);
                let input2_nid = self.visit(input2);
                let gate_nid = self.next_nid();
                // Modeling as `S := xor(A, B)` here:
                println!("{} xor 1 {} {}", gate_nid, input1_nid, input2_nid);
                gate_nid
            }
            Gate::CarryFullAdder { input1, input2, input3 } => {
                let input1_nid = self.visit(input1);
                let input2_nid = self.visit(input2);
                let input3_nid = self.visit(input3);
                let inner_xor_nid = self.next_nid();
                let inner_and1_nid = self.next_nid();
                let inner_and2_nid = self.next_nid();
                let gate_nid = self.next_nid();
                // Modeling as `C_out := or(and(xor(A, B), C_in), and(A, B))` here:
                println!("{} xor 1 {} {}", inner_xor_nid, input1_nid, input2_nid);
                println!("{} and 1 {} {}", inner_and1_nid, inner_xor_nid, input3_nid);
                println!("{} and 1 {} {}", inner_and2_nid, input1_nid, input2_nid);
                println!("{} or 1 {} {}", gate_nid, inner_and1_nid, inner_and2_nid);
                gate_nid
            }
            Gate::ResultFullAdder { input1, input2, input3 } => {
                let input1_nid = self.visit(input1);
                let input2_nid = self.visit(input2);
                let input3_nid = self.visit(input3);
                let inner_xor_nid = self.next_nid();
                let gate_nid = self.next_nid();
                // Modeling as `S := xor(xor(A, B), C_in)` here:
                println!("{} xor 1 {} {}", inner_xor_nid, input1_nid, input2_nid);
                println!("{} xor 1 {} {}", gate_nid, inner_xor_nid, input3_nid);
                gate_nid
            }
        }
    }
}

pub type GateRef = Rc<Gate>;
pub enum Gate {
    ConstTrue,
    ConstFalse,
    InputBit,
    Not {
        input: GateRef,
    },
    Bad {
        cond: GateRef,
    },
    And, 
    Nand, 
    Or, 
    Xnor, 
    Xor, 
    Matriarch1, 
    Matriarch2  {
        left: GateRef,
        right: GateRef,
    }
    AuxFullAdder, CarryFullAdder, ResultFullAdder {
        input1: GateRef,
        input2: GateRef,
        input3: GateRef
    }
    
}
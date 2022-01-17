use crate::PathBuf;
use std::cell::RefCell;
use std::collections::LinkedList;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::prelude::*;
use std::io::BufWriter;
use std::rc::Rc;

//
// Public Interface
//

pub mod builder;
pub mod memory;
pub mod optimize;
pub mod unroller;

pub type Nid = u64;
pub type NodeRef = Rc<RefCell<Node>>;

#[derive(Debug)]
pub enum Node {
    Const {
        nid: Nid,
        sort: NodeType,
        imm: u64,
    },
    Read {
        nid: Nid,
        memory: NodeRef,
        address: NodeRef,
    },
    Write {
        nid: Nid,
        memory: NodeRef,
        address: NodeRef,
        value: NodeRef,
    },
    Add {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Sub {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Mul {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Div {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Rem {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Ult {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Ext {
        nid: Nid,
        from: NodeType,
        value: NodeRef,
    },
    Ite {
        nid: Nid,
        sort: NodeType,
        cond: NodeRef,
        left: NodeRef,
        right: NodeRef,
    },
    Eq {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    And {
        nid: Nid,
        left: NodeRef,
        right: NodeRef,
    },
    Not {
        nid: Nid,
        value: NodeRef,
    },
    State {
        nid: Nid,
        sort: NodeType,
        init: Option<NodeRef>,
        name: Option<String>,
    },
    Next {
        nid: Nid,
        sort: NodeType,
        state: NodeRef,
        next: NodeRef,
    },
    Input {
        nid: Nid,
        sort: NodeType,
        name: String,
    },
    Bad {
        nid: Nid,
        cond: NodeRef,
        name: Option<String>,
    },
    Comment(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum NodeType {
    Bit,
    Word,
    Memory,
    Input1Byte,
    Input2Byte,
    Input3Byte,
    Input4Byte,
    Input5Byte,
    Input6Byte,
    Input7Byte,
}

#[derive(Debug)]
pub struct Model {
    // TODO: Switch from `LinkedList` to `Vec` here.
    pub lines: LinkedList<NodeRef>,
    pub sequentials: Vec<NodeRef>,
    pub bad_states_initial: Vec<NodeRef>,
    pub bad_states_sequential: Vec<NodeRef>,
    pub memory_size: u64,
    pub program_break: u64,
}

#[derive(Debug)]
pub struct HashableNodeRef {
    value: NodeRef,
}

#[rustfmt::skip]
pub fn print_model(model: &Model) {
    println!("; cksystemsgroup.github.io/monster\n");
    println!("1 sort bitvec 1 ; Boolean");
    println!("2 sort bitvec 64 ; 64-bit machine word");
    println!("3 sort array 2 2 ; 64-bit virtual memory");
    println!("11 sort bitvec 8 ; 1 byte");
    println!("12 sort bitvec 16 ; 2 bytes");
    println!("13 sort bitvec 24 ; 3 bytes");
    println!("14 sort bitvec 32 ; 4 bytes");
    println!("15 sort bitvec 40 ; 5 bytes");
    println!("16 sort bitvec 48 ; 6 bytes");
    println!("17 sort bitvec 56 ; 7 bytes");
    for node in model.lines.iter() {
        match &*node.borrow() {
            Node::Const { nid, sort, imm } =>
                println!("{} constd {} {}", nid, get_sort(sort), imm),
            Node::Read { nid, memory, address } =>
                println!("{} read 2 {} {}", nid, get_nid(memory), get_nid(address)),
            Node::Write { nid, memory, address, value } =>
                println!("{} write 3 {} {} {}", nid, get_nid(memory), get_nid(address), get_nid(value)),
            Node::Add { nid, left, right } =>
                println!("{} add 2 {} {}", nid, get_nid(left), get_nid(right)),
            Node::Sub { nid, left, right } =>
                println!("{} sub 2 {} {}", nid, get_nid(left), get_nid(right)),
            Node::Mul {nid, left, right} =>
                println!("{} mul 2 {} {}", nid, get_nid(left), get_nid(right)),
            Node::Div { nid, left, right } =>
                println!("{} udiv 2 {} {}", nid, get_nid(left), get_nid(right)),
            Node::Rem { nid, left, right } =>
                println!("{} urem 2 {} {}", nid, get_nid(left), get_nid(right)),
            Node::Ult { nid, left, right } =>
                println!("{} ult 1 {} {}", nid, get_nid(left), get_nid(right)),
            Node::Ext { nid, from, value } =>
                println!("{} uext 2 {} {}", nid, get_nid(value), 64 - get_bitsize(from)),
            Node::Ite { nid, sort, cond, left, right } =>
                println!("{} ite {} {} {} {}", nid, get_sort(sort), get_nid(cond), get_nid(left), get_nid(right)),
            Node::Eq { nid, left, right } =>
                println!("{} eq 1 {} {}", nid, get_nid(left), get_nid(right)),
            Node::And { nid, left, right } =>
                println!("{} and 1 {} {}", nid, get_nid(left), get_nid(right)),
            Node::Not { nid, value } =>
                println!("{} not 1 {}", nid, get_nid(value)),
            Node::State { nid, sort, init, name } => {
                println!("{} state {} {}", nid, get_sort(sort), name.as_deref().unwrap_or("?"));
                if let Some(value) = init {
                    println!("{} init {} {} {}", nid + 1, get_sort(sort), nid, get_nid(value));
                }
            }
            Node::Next { nid, sort, state, next } =>
                println!("{} next {} {} {}", nid, get_sort(sort), get_nid(state), get_nid(next)),
            Node::Input { nid, sort, name } =>
                println!("{} input {} {}", nid, get_sort(sort), name),
            Node::Bad { nid, cond, name } =>
                println!("{} bad {} {}", nid, get_nid(cond), name.as_deref().unwrap_or("?")),
            Node::Comment(s) =>
                println!("\n; {}\n", s),
        }
    }
    println!("\n; end of BTOR2 file");
}

#[rustfmt::skip]
pub fn write_model(model: &Model, output_path: PathBuf) -> std::io::Result<()> {
    let mut buffer = BufWriter::new(File::create(output_path)?);
    buffer.write_all(b"; cksystemsgroup.github.io/monster\n\n")?;
    buffer.write_all(b"1 sort bitvec 1 ; Boolean\n")?;
    buffer.write_all(b"2 sort bitvec 64 ; 64-bit machine word\n")?;
    buffer.write_all(b"3 sort array 2 2 ; 64-bit virtual memory\n")?;
    buffer.write_all(b"11 sort bitvec 8 ; 1 byte\n")?;
    buffer.write_all(b"12 sort bitvec 16 ; 2 bytes\n")?;
    buffer.write_all(b"13 sort bitvec 24 ; 3 bytes\n")?;
    buffer.write_all(b"14 sort bitvec 32 ; 4 bytes\n")?;
    buffer.write_all(b"15 sort bitvec 40 ; 5 bytes\n")?;
    buffer.write_all(b"16 sort bitvec 48 ; 6 bytes\n")?;
    buffer.write_all(b"17 sort bitvec 56 ; 7 bytes\n")?;
    for node in model.lines.iter() {
        match &*node.borrow() {
            Node::Const { nid, sort, imm } =>
                buffer.write_all(format!("{} constd {} {}\n", nid, get_sort(sort), imm).as_bytes())?,
            Node::Read { nid, memory, address } =>
                buffer.write_all(format!("{} read 2 {} {}\n", nid, get_nid(memory), get_nid(address)).as_bytes())?,
            Node::Write { nid, memory, address, value } =>
                buffer.write_all(format!("{} write 3 {} {} {}\n", nid, get_nid(memory), get_nid(address), get_nid(value)).as_bytes())?,
            Node::Add { nid, left, right } =>
                buffer.write_all(format!("{} add 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::Sub { nid, left, right } =>
                buffer.write_all(format!("{} sub 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::Mul {nid, left, right} =>
                buffer.write_all(format!("{} mul 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::Div { nid, left, right } =>
                buffer.write_all(format!("{} udiv 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::Rem { nid, left, right } =>
                buffer.write_all(format!("{} urem 2 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::Ult { nid, left, right } =>
                buffer.write_all(format!("{} ult 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::Ext { nid, from, value } =>
                buffer.write_all(format!("{} uext 2 {} {}\n", nid, get_nid(value), 64 - get_bitsize(from)).as_bytes())?,
            Node::Ite { nid, sort, cond, left, right } =>
                buffer.write_all(format!("{} ite {} {} {} {}\n", nid, get_sort(sort), get_nid(cond), get_nid(left), get_nid(right)).as_bytes())?,
            Node::Eq { nid, left, right } =>
                buffer.write_all(format!("{} eq 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::And { nid, left, right } =>
                buffer.write_all(format!("{} and 1 {} {}\n", nid, get_nid(left), get_nid(right)).as_bytes())?,
            Node::Not { nid, value } =>
                buffer.write_all(format!("{} not 1 {}\n", nid, get_nid(value)).as_bytes())?,
            Node::State { nid, sort, init, name } => {
                buffer.write_all(format!("{} state {} {}\n", nid, get_sort(sort), name.as_deref().unwrap_or("?")).as_bytes())?;
                if let Some(value) = init {
                    buffer.write_all(format!("{} init {} {} {}\n", nid + 1, get_sort(sort), nid, get_nid(value)).as_bytes())?;
                }
            }
            Node::Next { nid, sort, state, next } =>
                buffer.write_all(format!("{} next {} {} {}\n", nid, get_sort(sort), get_nid(state), get_nid(next)).as_bytes())?,
            Node::Input { nid, sort, name } =>
                buffer.write_all(format!("{} input {} {}\n", nid, get_sort(sort), name).as_bytes())?,
            Node::Bad { nid, cond, name } =>
                buffer.write_all(format!("{} bad {} {}\n", nid, get_nid(cond), name.as_deref().unwrap_or("?")).as_bytes())?,
            Node::Comment(s) =>
                buffer.write_all(format!("\n\n; {}\n\n", s).as_bytes())?,
        }
    }
    buffer.write_all(b"\n\n; end of BTOR2 file")?;
    buffer.flush()?;
    Ok(())
}

//
// Private Implementation
//

fn get_nid(node: &NodeRef) -> Nid {
    match *node.borrow() {
        Node::Const { nid, .. } => nid,
        Node::Read { nid, .. } => nid,
        Node::Write { nid, .. } => nid,
        Node::Add { nid, .. } => nid,
        Node::Sub { nid, .. } => nid,
        Node::Mul { nid, .. } => nid,
        Node::Div { nid, .. } => nid,
        Node::Rem { nid, .. } => nid,
        Node::Ult { nid, .. } => nid,
        Node::Ext { nid, .. } => nid,
        Node::Ite { nid, .. } => nid,
        Node::Eq { nid, .. } => nid,
        Node::And { nid, .. } => nid,
        Node::Not { nid, .. } => nid,
        Node::State { nid, .. } => nid,
        Node::Next { nid, .. } => nid,
        Node::Input { nid, .. } => nid,
        Node::Bad { nid, .. } => nid,
        Node::Comment(_) => panic!("has no nid"),
    }
}

fn get_sort(sort: &NodeType) -> Nid {
    match *sort {
        NodeType::Bit => 1,
        NodeType::Word => 2,
        NodeType::Memory => 3,
        NodeType::Input1Byte => 11,
        NodeType::Input2Byte => 12,
        NodeType::Input3Byte => 13,
        NodeType::Input4Byte => 14,
        NodeType::Input5Byte => 15,
        NodeType::Input6Byte => 16,
        NodeType::Input7Byte => 17,
    }
}

fn get_bitsize(sort: &NodeType) -> usize {
    match *sort {
        NodeType::Bit => 1,
        NodeType::Input1Byte => 8,
        NodeType::Input2Byte => 16,
        NodeType::Input3Byte => 24,
        NodeType::Input4Byte => 32,
        NodeType::Input5Byte => 40,
        NodeType::Input6Byte => 48,
        NodeType::Input7Byte => 56,
        _ => panic!("unknown bitsize"),
    }
}

impl Eq for HashableNodeRef {}

impl From<NodeRef> for HashableNodeRef {
    fn from(node: NodeRef) -> Self {
        Self { value: node }
    }
}

impl Hash for HashableNodeRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        RefCell::as_ptr(&self.value).hash(state);
    }
}

impl PartialEq for HashableNodeRef {
    fn eq(&self, other: &Self) -> bool {
        RefCell::as_ptr(&self.value) == RefCell::as_ptr(&other.value)
    }
}

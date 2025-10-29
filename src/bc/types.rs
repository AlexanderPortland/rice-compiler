//! Type definitions for the bytecode.

use std::{borrow::Borrow, collections::HashMap, sync::Arc};

use either::Either;
use indexical::IndexedDomain;
use internment::Intern;
use itertools::Itertools;
use petgraph::{
    Direction,
    graph::{DiGraph, NodeIndex},
};
use serde::Serialize;
use smallvec::{SmallVec, smallvec};
use strum::Display;

use crate::{
    ast::types::{Annotation, Span},
    interned,
    utils::{self, Symbol},
};

pub use crate::tir::types::{Binop, Const, Type, TypeKind};

#[derive(Debug, Clone, Serialize)]
pub struct Program(Vec<Function>);

impl Program {
    #[must_use]
    pub fn new(funcs: Vec<Function>) -> Self {
        Program(funcs)
    }

    #[must_use]
    pub fn functions(&self) -> &[Function] {
        &self.0
    }

    /// NOTE: returns none if the function's defined within the standard library.
    pub fn find_function(&self, sym: impl Borrow<Symbol>) -> Option<&Function> {
        let sym = sym.borrow();
        let matching = self
            .functions()
            .into_iter()
            .filter(|func| func.name == *sym)
            .collect::<Vec<_>>();

        if matching.is_empty() {
            return None;
        }

        assert!(
            matching.len() == 1,
            "we should only have a single function named, {sym}"
        );
        Some(matching[0])
    }

    pub fn main_function(&self) -> &Function {
        self.find_function(Symbol::main())
            .expect("we should have a main function")
    }

    pub fn functions_mut(&mut self) -> &mut [Function] {
        &mut self.0
    }

    #[must_use]
    pub fn into_functions(self) -> Vec<Function> {
        self.0
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug, Serialize)]
pub struct Local {
    /// The type of the local variable.
    pub ty: Type,

    /// A source-level name for the local variable, if it exists.
    pub name: Option<Symbol>,
}

indexical::define_index_type! {
    /// An index for locals, for use in indexical data structures.
    pub struct LocalIdx for Local = u32;
}

#[derive(Debug, Clone, Serialize)]
pub struct Function {
    /// The global name of the function. Must be unique.
    pub name: Symbol,

    /// The first `num_param` locals are parameters.
    pub num_params: usize,

    /// All the local variables in the function.
    pub locals: Arc<IndexedDomain<Local>>,

    /// The return type.
    pub ret_ty: Type,

    /// The control-flow graph of instructions.
    pub body: Body,

    /// Source-level annotations attached to this function.
    pub annots: Vec<Annotation>,
}

impl Function {
    /// Returns an iterator over the local index and type of each parameter.
    pub fn params(&self) -> impl Iterator<Item = (LocalIdx, Type)> {
        (0..self.num_params).map(|i| {
            let local = LocalIdx::from_usize(i);
            (local, self.locals.value(local).ty)
        })
    }

    /// Returns true if the function is annotated with `#[jit]`.
    #[must_use]
    pub fn jit(&self) -> bool {
        self.annots.iter().any(|annot| annot.name == "jit")
    }

    /// Returns true if the function is annotated with `#[secure]`.
    #[must_use]
    pub fn secure(&self) -> bool {
        self.annots.iter().any(|annot| annot.name == "secure")
    }
}

pub type Cfg = DiGraph<BasicBlock, ()>;

#[derive(Debug, Clone, Default, Serialize)]
pub struct Body {
    /// The instructions in the body.    
    cfg: Cfg,

    /// A set of all locations in the body, useful for maps indexed by location.
    locations: Arc<IndexedDomain<Location>>,

    /// Reverse-postorder traversal of basic blocks in the CFG.    
    #[serde(skip)]
    rpo: Vec<BasicBlockIdx>,
}

impl Body {
    pub fn new(cfg: Cfg) -> Self {
        let rpo = utils::reverse_post_order(&cfg, Location::START.block.into())
            .into_iter()
            .map(BasicBlockIdx::from)
            .collect_vec();

        let locations = Self::build_domain(&cfg, &rpo);

        Body {
            cfg,
            locations,
            rpo,
        }
    }

    fn build_domain(cfg: &Cfg, rpo: &[BasicBlockIdx]) -> Arc<IndexedDomain<Location>> {
        Arc::new(
            rpo.iter()
                .copied()
                .flat_map(|block| {
                    // println!("building domain for block {:?}", block);
                    let num_instrs = cfg.node_weight(block.into()).unwrap().statements.len() + 1;
                    (0..num_instrs).map(move |instr| Location { block, instr })
                })
                .collect(),
        )
    }

    fn block_is_redundant(&self, block_no: BasicBlockIdx, min_connections: usize) -> bool {
        self.cfg()
            .neighbors_directed(block_no.into(), petgraph::Direction::Incoming)
            .count()
            <= min_connections
            && block_no != 0
    }

    /// Shadow remove a basic block from this body's structure. Removes all nodes that it points to
    /// but doesn't actually remove the block itself to preserve indexing. But nothing will point to it so doesn't really matter.
    pub fn remove_block_cfg_edges(&mut self, block_no: BasicBlockIdx) {
        // println!("remove {:?}", block_no);
        assert_eq!(
            self.cfg()
                .neighbors_directed(block_no.into(), petgraph::Direction::Incoming)
                .count(),
            0
        );
        assert_ne!(block_no, 0, "dont try to remove the first block you dofus");

        // clear all the statments, as we'll remove this block
        self.data_mut(block_no).statements.clear();

        // remove all neighbors in the cfg
        for out_neighbor in self
            .cfg()
            .neighbors_directed(block_no.into(), petgraph::Direction::Outgoing)
            .collect::<Vec<_>>()
        {
            // if this neighbor only has one incoming connection (us), we want to remove them too...

            let edge = self
                .cfg()
                .find_edge(block_no.into(), out_neighbor)
                .expect("should have an edge to all neighbors");
            self.cfg_mut()
                .remove_edge(edge)
                .expect("should have an edge here..");

            if self.block_is_redundant(out_neighbor.into(), 0) {
                self.remove_block_cfg_edges(out_neighbor.into());
            }
        }
    }

    /// Regenerates the rpo, domain and locations. For use when adding or remove basic blocks.
    pub fn regenerate_everything(&mut self) {
        // I think just reconstructing it should work...
        *self = Self::new(std::mem::take(&mut self.cfg));
    }

    /// Regenerates the location domain, to be used after adding or removing instructions.
    pub fn regenerate_domain(&mut self) {
        self.locations = Self::build_domain(&self.cfg, &self.rpo);
    }

    /// Returns the data corresponding to the given basic block.
    #[must_use]
    pub fn data(&self, node: BasicBlockIdx) -> &BasicBlock {
        self.cfg.node_weight(node.into()).unwrap()
    }

    /// Returns a mutable handle to the data in a given basic block.
    pub fn data_mut(&mut self, node: BasicBlockIdx) -> &mut BasicBlock {
        self.cfg.node_weight_mut(node.into()).unwrap()
    }

    /// Returns an iterator over basic block indices.
    ///
    /// Guaranteed to be a reverse-postorder.
    #[must_use]
    pub fn blocks(&self) -> impl DoubleEndedIterator<Item = BasicBlockIdx> {
        self.rpo.iter().copied()
    }

    /// Returns the underlying CFG.
    #[must_use]
    pub fn cfg(&self) -> &Cfg {
        &self.cfg
    }

    /// Returns the underlying CFG.
    pub fn cfg_mut(&mut self) -> &mut Cfg {
        &mut self.cfg
    }

    /// Returns the location domain.
    #[must_use]
    pub fn locations(&self) -> &Arc<IndexedDomain<Location>> {
        &self.locations
    }

    /// Returns the instruction at a given location.
    #[must_use]
    pub fn instr(&self, loc: Location) -> Either<&Statement, &Terminator> {
        self.data(loc.block).get(loc.instr)
    }

    /// Returns a mutable handle to the instruction at a given locatin.
    pub fn instr_mut(&mut self, loc: Location) -> Either<&mut Statement, &mut Terminator> {
        self.data_mut(loc.block).get_mut(loc.instr)
    }

    /// Returns all locations which can possibly come after the given location.
    #[must_use]
    pub fn successors(&self, loc: Location) -> SmallVec<[Location; 2]> {
        if loc.instr == self.data(loc.block).terminator_index() {
            self.cfg
                .neighbors_directed(loc.block.into(), Direction::Outgoing)
                .map(|block| Location {
                    block: BasicBlockIdx::from(block),
                    instr: 0,
                })
                .collect()
        } else {
            smallvec![Location {
                block: loc.block,
                instr: loc.instr + 1,
            }]
        }
    }

    /// Returns all locations which can possibly come before the given location.
    #[must_use]
    pub fn predecessors(&self, loc: Location) -> SmallVec<[Location; 2]> {
        if loc.instr == 0 {
            self.cfg
                .neighbors_directed(loc.block.into(), Direction::Incoming)
                .map(|block| {
                    let block = BasicBlockIdx::from(block);
                    let instr = self.data(block).terminator_index();
                    Location { block, instr }
                })
                .collect()
        } else {
            smallvec![Location {
                block: loc.block,
                instr: loc.instr - 1
            }]
        }
    }
}

index_vec::define_index_type! {
    pub struct BasicBlockIdx = u32;
}

impl BasicBlockIdx {
    /// Returns the location of the first instruction in the basic block.
    #[must_use]
    pub fn entry(self) -> Location {
        Location {
            block: self,
            instr: 0,
        }
    }
}

impl From<NodeIndex> for BasicBlockIdx {
    fn from(value: NodeIndex) -> Self {
        BasicBlockIdx::new(value.index())
    }
}

impl From<BasicBlockIdx> for NodeIndex {
    fn from(value: BasicBlockIdx) -> Self {
        NodeIndex::new(value.index())
    }
}

/// A coordinate for a particular instruction in a CFG.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct Location {
    /// The basic block containing the instruction.
    pub block: BasicBlockIdx,

    /// The index of the instruction within the basic block.
    pub instr: usize,
}

indexical::define_index_type! {
    pub struct LocationIdx for Location = u32;
}

impl Location {
    /// The location of the starting instruction in any CFG.
    pub const START: Location = Location {
        block: BasicBlockIdx { _raw: 0 },
        instr: 0,
    };
}

/// A basic block in the control flow graph, containing a sequence of statements followed by a terminator.
#[derive(Debug, Clone, Serialize)]
pub struct BasicBlock {
    /// Statements executed in sequence.
    pub statements: Vec<Statement>,

    /// The final instruction, which can branch to other basic blocks.
    pub terminator: Terminator,
}

impl BasicBlock {
    /// Get the ith instruction in the basic block.
    #[must_use]
    pub fn get(&self, i: usize) -> Either<&Statement, &Terminator> {
        assert!(i <= self.statements.len());
        if i == self.statements.len() {
            Either::Right(&self.terminator)
        } else {
            Either::Left(&self.statements[i])
        }
    }

    // Get a mutable handle to the ith instruction in the basic block.
    pub fn get_mut(&mut self, i: usize) -> Either<&mut Statement, &mut Terminator> {
        assert!(i <= self.statements.len());
        if i == self.statements.len() {
            Either::Right(&mut self.terminator)
        } else {
            Either::Left(&mut self.statements[i])
        }
    }

    #[must_use]
    pub fn terminator_index(&self) -> usize {
        self.statements.len()
    }
}

/// An instruction of the form `place = rvalue`.
#[derive(Debug, Clone, Serialize)]
pub struct Statement {
    /// The place in memory being assigned to.
    pub place: Place,

    /// An expression that generates a value to set to the place.
    pub rvalue: Rvalue,

    /// A best-effort source-level span for the statement.
    pub span: Span,
}

/// An argument to an [`Rvalue`].
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub enum Operand {
    Const(Const),
    Place(Place),
    Func { f: Symbol, ty: Type },
}

impl Operand {
    #[must_use]
    pub fn ty(&self) -> Type {
        match self {
            Operand::Place(p) => p.ty,
            Operand::Const(c) => c.ty(),
            Operand::Func { ty, .. } => *ty,
        }
    }

    #[must_use]
    pub fn as_place(&self) -> Option<Place> {
        match self {
            Operand::Place(p) => Some(*p),
            _ => None,
        }
    }
}

/// The kind of object allocated by an [`Rvalue::Alloc`] instruction.
#[derive(Debug, Clone, Copy, Display, Serialize)]
pub enum AllocKind {
    Struct,
    Tuple,
    Array,
}

/// The location in memory of an object allocated by an [`Rvalue::Alloc`] instruction.
#[derive(Debug, Clone, Copy, Display, Serialize, PartialEq, Eq, PartialOrd, Ord)]
// #[serde(rename_all = "lowercase")]
#[serde(into = "String")]
pub enum AllocLoc {
    Stack,
    Heap,
}

impl From<AllocLoc> for String {
    fn from(value: AllocLoc) -> Self {
        format!("{value}")
    }
}

/// The inputs to an allocation by an [`Rvalue::Alloc`] instruction.
#[derive(Debug, Clone, Display, Serialize)]

pub enum AllocArgs {
    /// A fixed-size literal, e.g. `(x, y)` or `[x, y]`.
    Lit(Vec<Operand>),
    Repeated {
        op: Operand,
        count: Operand,
    },
}

/// An expression that is assigned to a [`Place`] in a [`Statement`].
#[derive(Debug, Clone, Serialize)]
pub enum Rvalue {
    /// The direct value of an operand, e.g. `1` or `x`.
    Operand(Operand),

    /// Cast another operand to a new type, e.g. `x as float`.
    Cast { op: Operand, ty: Type },

    /// A first-class function with a (potentially-empty) environment, e.g., `closure(lambda, [x, y])`.
    Closure { f: Symbol, env: Vec<Operand> },

    /// An allocation of a data structure larger than a register.
    Alloc {
        kind: AllocKind,
        loc: AllocLoc,
        args: AllocArgs,
    },

    /// A binary operator.
    Binop {
        op: Binop,
        left: Operand,
        right: Operand,
    },

    /// A call to a non-method function.
    Call { f: Operand, args: Vec<Operand> },

    /// A call to a method function w/ dynamic dispatch.
    MethodCall {
        /// The object containing a vtable.
        receiver: Operand,

        /// The index of the vtable to lookup.
        method: usize,

        /// The arguments to the method.
        args: Vec<Operand>,
    },
}

impl Rvalue {
    /// Returns a vector of all the places used in the rvalue.
    #[must_use]
    pub fn places(&self) -> SmallVec<[Place; 2]> {
        match self {
            Rvalue::Operand(op) | Rvalue::Cast { op, .. } => op.as_place().into_iter().collect(),
            Rvalue::Alloc { args, .. } => match args {
                AllocArgs::Lit(ops) => ops.iter().filter_map(Operand::as_place).collect(),
                AllocArgs::Repeated { op, count } => vec![op.as_place(), count.as_place()]
                    .into_iter()
                    .flatten()
                    .collect(),
            },
            Rvalue::Call { args: ops, .. } | Rvalue::Closure { env: ops, .. } => {
                ops.iter().filter_map(Operand::as_place).collect()
            }
            Rvalue::MethodCall { receiver, args, .. } => args
                .iter()
                .chain([receiver])
                .filter_map(Operand::as_place)
                .collect(),
            Rvalue::Binop { left, right, .. } => left
                .as_place()
                .into_iter()
                .chain(right.as_place())
                .collect(),
        }
    }
}

/// The final instruction in a basic block.
#[derive(Debug, Clone, Serialize)]
pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span,
}

impl Terminator {
    #[must_use]
    pub fn kind(&self) -> &TerminatorKind {
        &self.kind
    }

    pub fn kind_mut(&mut self) -> &mut TerminatorKind {
        &mut self.kind
    }

    pub fn places(&self) -> SmallVec<[Place; 2]> {
        match &self.kind {
            TerminatorKind::Return(op) | TerminatorKind::CondJump { cond: op, .. } => {
                op.as_place().into_iter().collect()
            }
            TerminatorKind::Jump(_) => SmallVec::new(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub enum TerminatorKind {
    /// Return the value of the operand from the function.
    Return(Operand),

    /// Unconditionally jump to the given basic block.
    Jump(BasicBlockIdx),

    /// Conditionally jump to `true_` if `cond` is true, and jump to `false_` otherwise.
    CondJump {
        cond: Operand,
        true_: BasicBlockIdx,
        false_: BasicBlockIdx,
    },
}

impl Terminator {
    /// Remap the basic blocks inside the terminator, used during CFG construction.
    pub fn remap(&mut self, map: &HashMap<BasicBlockIdx, BasicBlockIdx>) {
        match &mut self.kind {
            TerminatorKind::Jump(block) => *block = map[block],
            TerminatorKind::CondJump { true_, false_, .. } => {
                *true_ = map[true_];
                *false_ = map[false_];
            }
            TerminatorKind::Return(..) => {}
        }
    }
}

/// A reference to a particular location in memory relative to a particular function.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct PlaceData {
    /// The root of the reference, a local on a stack frame.
    pub local: LocalIdx,

    /// A sequence of projections off of the local.
    pub projection: Vec<ProjectionElem>,

    /// The type of the data at the location.
    pub ty: Type,
}

interned!(Place, PlaceData);

impl Place {
    #[must_use]
    pub fn new(local: LocalIdx, projection: Vec<ProjectionElem>, ty: Type) -> Self {
        Place(Intern::new(PlaceData {
            local,
            projection,
            ty,
        }))
    }

    #[must_use]
    pub fn extend_projection(
        self,
        elems: impl IntoIterator<Item = ProjectionElem>,
        ty: Type,
    ) -> Self {
        let mut projection = self.projection.clone();
        projection.extend(elems);
        Place::new(self.local, projection, ty)
    }
}

/// A lookup into a field of a data structure.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub enum ProjectionElem {
    /// Get the field of a fixed-sized structure.
    Field { index: usize, ty: Type },

    /// Index into a fixed-size array.
    Index { index: Operand, ty: Type },
}

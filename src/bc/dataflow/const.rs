use crate::{
    ast::types as ast,
    bc::{
        dataflow::{self, Analysis, JoinSemiLattice, analyze_to_fixpoint},
        types::{Binop, Const, Function, Local, Location, Operand, Rvalue, Statement, Type},
        visit::{Visit, VisitMut},
    },
    rt,
    utils::Symbol,
};
use indexical::{
    ArcIndexSet, ArcIndexVec, RcIndexSet, ToIndex, pointer::PointerFamily, vec::IndexVec,
};
use itertools::Itertools;

pub fn const_prop(func: &mut Function) -> bool {
    let analysis_result = analyze_to_fixpoint(&ConstAnalysis, func);

    for location in func.body.locations().indices() {
        // println!("at location {:?}", location);
        let domain_here = &analysis_result[location];
        for local in func.locals.indices() {
            // println!("\tlocal {:?} has info {:?}", local, domain_here[local]);
        }
    }
    let mut propogator = ConstProp::new(&analysis_result);
    propogator.visit_function(func);
    propogator.any_change
}

pub struct ConstProp<'z> {
    info: &'z ArcIndexVec<Location, ArcIndexVec<Local, ConstInfo>>,
    any_change: bool,
}

impl<'z> ConstProp<'z> {
    fn new(info: &'z ArcIndexVec<Location, ArcIndexVec<Local, ConstInfo>>) -> Self {
        Self {
            info,
            any_change: false,
        }
    }
}

impl VisitMut for ConstProp<'_> {
    fn visit_operand(&mut self, operand: &mut Operand, loc: Location) {
        if let Operand::Place(p) = operand
            && p.projection.is_empty()
            && let ConstInfo::Const(c) = self.info.get(loc).get(p.local).clone()
        {
            self.any_change |= true;
            *operand = Operand::Const(c)
        }
        self.super_visit_operand(operand, loc);
    }

    fn visit_statement(&mut self, stmt: &mut Statement, loc: Location) {
        if let Rvalue::Call {
            f: Operand::Place(p_fun),
            args,
        } = stmt.rvalue.clone()
            && p_fun.projection.is_empty()
            && let ConstInfo::Closure(closure_symbol) = self.info.get(loc).get(p_fun.local).clone()
        {
            let fn_ty = Type::func(
                args.iter().map(|a| a.ty()).collect::<Vec<_>>(),
                stmt.place.ty,
            );
            stmt.rvalue = Rvalue::Call {
                f: Operand::Func {
                    f: closure_symbol,
                    ty: fn_ty,
                },
                args,
            }
        }

        self.super_visit_statement(stmt, loc);
    }
}

pub struct ConstAnalysis;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstInfo {
    Unknown, // BOTTOM - known nothing
    Const(ast::Const),
    // Func(Symbol, Type),
    Closure(Symbol),
    Variable, // TOP - know too much
}

impl ConstInfo {
    fn get_const(self) -> Option<ast::Const> {
        if let Self::Const(c) = self {
            Some(c)
        } else {
            None
        }
    }
}

impl PartialOrd for ConstInfo {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Unknown, Self::Unknown) => Some(std::cmp::Ordering::Equal),
            (Self::Variable, Self::Variable) => Some(std::cmp::Ordering::Equal),
            (Self::Unknown, _) | (_, Self::Variable) => Some(std::cmp::Ordering::Less),
            (_, Self::Unknown) | (Self::Variable, _) => Some(std::cmp::Ordering::Greater),
            _ => None,
        }
    }
}

impl JoinSemiLattice for ArcIndexVec<Local, ConstInfo> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (my_info, new_info) in self.iter_mut().zip(other.iter()) {
            // println!("i have {:?}, they have {:?}", my_info, new_info);
            if my_info == new_info {
                // println!("we match!");
                continue;
            }

            match (*my_info).partial_cmp(new_info) {
                Some(std::cmp::Ordering::Less) => {
                    changed |= true;
                    *my_info = new_info.clone()
                }
                None => {
                    changed |= true;
                    *my_info = ConstInfo::Variable
                }
                _ => (),
            }
            // println!("now we have {:?}", my_info);
        }
        changed
    }
}

impl ConstAnalysis {
    fn const_eval_rvalue(state: &<Self as Analysis>::Domain, rvalue: &Rvalue) -> Option<ConstInfo> {
        match rvalue {
            Rvalue::Operand(op) => Self::const_eval_operand(state, op),
            Rvalue::Binop { op, left, right } => Self::const_eval_binop(state, op, left, right),
            Rvalue::Cast { op, ty } => todo!(),
            Rvalue::Closure { f, env } => {
                if env.is_empty() {
                    Some(ConstInfo::Closure(*f))
                } else {
                    None
                }
            }
            // ^^All this should be todo
            Rvalue::Alloc { .. } | Rvalue::Call { .. } | Rvalue::MethodCall { .. } => None,
        }
    }

    fn do_int_op_on_consts_inner(left: Const, right: Const, op: impl Fn(i32, i32) -> i32) -> Const {
        let left = left.as_int().expect("should be int");
        let right = right.as_int().expect("should be int");
        Const::Int(op(left, right))
    }

    fn do_int_op_on_consts(
        left: Const,
        right: Const,
        op: impl Fn(i32, i32) -> i32,
    ) -> Option<ConstInfo> {
        Some(ConstInfo::Const(Self::do_int_op_on_consts_inner(
            left, right, op,
        )))
    }

    fn const_eval_binop(
        state: &<Self as Analysis>::Domain,
        op: &Binop,
        left: &Operand,
        right: &Operand,
    ) -> Option<ConstInfo> {
        let Some(ConstInfo::Const(left)) = Self::const_eval_operand(state, left) else {
            return None;
        };

        let Some(ConstInfo::Const(right)) = Self::const_eval_operand(state, right) else {
            return None;
        };

        match op {
            Binop::Add => Self::do_int_op_on_consts(left, right, i32::wrapping_add),
            _ => None,
        }
    }

    fn const_eval_operand(state: &<Self as Analysis>::Domain, op: &Operand) -> Option<ConstInfo> {
        match op {
            Operand::Const(c) => Some(ConstInfo::Const(c.clone())),
            Operand::Place(p) => {
                if p.projection.is_empty() {
                    Some(state.get(p.local).clone())
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl Analysis for ConstAnalysis {
    const DIRECTION: dataflow::Direction = dataflow::Direction::Forward;
    type Domain = ArcIndexVec<Local, ConstInfo>;

    fn bottom(&self, func: &Function) -> Self::Domain {
        ArcIndexVec::from_elem(ConstInfo::Unknown, &func.locals)
    }

    fn handle_statement(&self, state: &mut Self::Domain, statement: &Statement, loc: Location) {
        let assigned_local = statement.place.local;
        if let Some(const_val) = Self::const_eval_rvalue(state, &statement.rvalue)
            && statement.place.projection.is_empty()
        {
            state[assigned_local] = const_val;
        } else {
            // Don't do anything. It's either not const eval or it's going into a projected place
        }
    }

    fn handle_terminator(
        &self,
        state: &mut Self::Domain,
        terminator: &crate::bc::types::Terminator,
        loc: Location,
    ) {
    }
}

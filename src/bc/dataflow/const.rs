use crate::{
    ast::types as ast,
    bc::{
        dataflow::{self, Analysis, JoinSemiLattice, analyze_to_fixpoint},
        types::{
            Binop, Const, Function, Local, Location, Operand, Rvalue, Statement, TerminatorKind,
            Type,
        },
        visit::{Visit, VisitMut},
    },
    rt,
    utils::Symbol,
};
use core::ops::*;
use indexical::{
    ArcIndexSet, ArcIndexVec, RcIndexSet, ToIndex, pointer::PointerFamily, vec::IndexVec,
};
use itertools::Itertools;

/// Propagates constants throughout the program, filling in their value.
///
/// Also simplifies control flow if a conditional jump can be determined to only ever take one branch.
pub fn const_prop(func: &mut Function) -> bool {
    let analysis_result = analyze_to_fixpoint(&ConstAnalysis, func);

    // Build and use a visitor to replace places using the result of our analysis.
    let mut propagator = ConstProp::new(&analysis_result);
    propagator.visit_function(func);
    propagator.any_change
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

    fn visit_body(&mut self, body: &mut crate::bc::types::Body) {
        let cfg = body.cfg_mut();

        let b = body.blocks().collect::<Vec<_>>();
        for block in b {
            let data = body.data_mut(block);

            let loc = Location {
                block,
                instr: data.terminator_index(),
            };
            let term = &mut data.terminator;

            // I do not remember what shit i was on when i wrote this.
            if let Some((always_jump_to, never_jump_to)) = if let TerminatorKind::CondJump {
                cond: Operand::Place(p_cond),
                true_,
                false_,
            } = term.kind()
                && p_cond.projection.is_empty()
                && let ConstInfo::Const(Const::Bool(const_cond)) =
                    self.info.get(loc).get(p_cond.local)
            {
                if *const_cond {
                    Some((*true_, *false_))
                } else {
                    Some((*false_, *true_))
                }
            } else if let TerminatorKind::CondJump {
                cond: Operand::Const(c),
                true_,
                false_,
            } = term.kind()
                && let Const::Bool(const_cond) = c
            {
                if *const_cond {
                    Some((*true_, *false_))
                } else {
                    Some((*false_, *true_))
                }
            } else {
                None
            } {
                term.kind = TerminatorKind::Jump(always_jump_to);
                let edge_index = body
                    .cfg_mut()
                    .find_edge(block.into(), never_jump_to.into())
                    .expect("there should be an edge here...");
                let rem = body.cfg_mut().remove_edge(edge_index);
                if rem.is_none() {
                    panic!("ahhhh");
                }
            }
        }

        self.super_visit_body(body);
    }

    fn visit_terminator(&mut self, term: &mut crate::bc::types::Terminator, loc: Location) {
        self.super_visit_terminator(term, loc);
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
            if my_info == new_info {
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
        }
        changed
    }
}

impl ConstAnalysis {
    fn const_eval_rvalue(state: &<Self as Analysis>::Domain, rvalue: &Rvalue) -> Option<ConstInfo> {
        // println!("eval rvalue {:?}", rvalue);
        match rvalue {
            Rvalue::Operand(op) => Self::const_eval_operand(state, op),
            Rvalue::Binop { op, left, right } => Self::const_eval_binop(state, op, left, right),
            Rvalue::Cast { op, ty } => Self::const_eval_cast(state, op, ty),
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

    fn const_eval_cast(
        state: &<Self as Analysis>::Domain,
        op: &Operand,
        cast_to: &Type,
    ) -> Option<ConstInfo> {
        // println!("casing op {:?} to {:?}", op, cast_to);
        // todo!()
        // TODO: can this be const eval-ed?
        None
    }

    fn const_eval_binop(
        state: &<Self as Analysis>::Domain,
        op: &Binop,
        left: &Operand,
        right: &Operand,
    ) -> Option<ConstInfo> {
        // println!("const eval binop {:?} on {:?} {:?}", op, left, right);
        let (left, right) = match (
            Self::const_eval_operand(state, left),
            Self::const_eval_operand(state, right),
        ) {
            (Some(ConstInfo::Unknown), Some(ConstInfo::Unknown)) => {
                return Some(ConstInfo::Unknown);
            }
            (Some(ConstInfo::Variable), Some(_)) | (Some(_), Some(ConstInfo::Variable)) => {
                return Some(ConstInfo::Variable);
            }
            (Some(ConstInfo::Const(left)), Some(ConstInfo::Const(right))) => (left, right),
            _ => return None,
        };

        if right.ty() != left.ty() {
            panic!("weird typing shit");
        }

        let new_const = match (left, right) {
            (Const::Bool(left), Const::Bool(right)) => Const::Bool(match op {
                Binop::And => left && right,
                Binop::Or => left || right,
                Binop::Eq => left == right,
                Binop::Neq => left != right,
                _ => return None,
            }),
            (Const::Int(left), Const::Int(right)) => {
                let op = match op {
                    Binop::Add => i32::wrapping_add,
                    Binop::Sub => i32::wrapping_sub,
                    Binop::Mul => i32::wrapping_mul,
                    Binop::Div => i32::wrapping_div,
                    Binop::Rem => i32::wrapping_rem,
                    Binop::Exp => |left, right| i32::pow(left, right as u32),
                    Binop::Shl => |left, right| i32::wrapping_shl(left, right as u32),
                    Binop::Shr => |left, right| i32::wrapping_shr(left, right as u32),
                    Binop::BitOr => |left, right| left | right,
                    Binop::BitAnd => |left, right| left & right,

                    _ => {
                        let ret_bool_op = match op {
                            Binop::Ge => |left, right| i32::ge(&left, &right),
                            Binop::Gt => |left, right| i32::gt(&left, &right),
                            Binop::Le => |left, right| i32::le(&left, &right),
                            Binop::Lt => |left, right| i32::lt(&left, &right),
                            Binop::Eq => |left, right| i32::eq(&left, &right),
                            Binop::Neq => |left, right| i32::ne(&left, &right),
                            _ => return None,
                        };
                        return Some(ConstInfo::Const(Const::Bool(ret_bool_op(left, right))));
                    }
                };
                Const::Int(op(left, right))
            }
            (Const::Float(left), Const::Float(right)) => {
                let op = match op {
                    Binop::Add => f32::add,
                    Binop::Sub => f32::sub,
                    Binop::Mul => f32::mul,
                    Binop::Div => f32::div,
                    Binop::Rem => |left, right| left % right,
                    Binop::Exp => f32::powf,

                    _ => {
                        let ret_bool_op = match op {
                            Binop::Ge => |left, right| f32::ge(&left, &right),
                            Binop::Gt => |left, right| f32::gt(&left, &right),
                            Binop::Le => |left, right| f32::le(&left, &right),
                            Binop::Lt => |left, right| f32::lt(&left, &right),
                            Binop::Eq => |left, right| f32::eq(&left, &right),
                            Binop::Neq => |left, right| f32::ne(&left, &right),
                            _ => return None,
                        };
                        return Some(ConstInfo::Const(Const::Bool(ret_bool_op(*left, *right))));
                    }
                };
                Const::Float(op(*left, *right).into())
            }
            (Const::String(left), Const::String(right)) => match op {
                Binop::Concat => Const::String(left + &right),
                _ => return None,
            },
            _ => return None,
        };

        Some(ConstInfo::Const(new_const))
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
        if statement.place.projection.is_empty() {
            // Ignore projected places
            if let Some(const_val) = Self::const_eval_rvalue(state, &statement.rvalue) {
                state[assigned_local] = const_val;
            } else {
                // If we can't compute it const, it's variable
                // state[assigned_local] = ConstInfo::Variable;
            }
        }
    }

    fn handle_terminator(
        &self,
        state: &mut Self::Domain,
        terminator: &crate::bc::types::Terminator,
        loc: Location,
    ) {
        // do nothing
    }
}

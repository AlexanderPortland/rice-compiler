//! Desugars while-loops and if-statements.

use super::{
    types::{Expr, ExprKind, Program, Type},
    visit::VisitMut,
};

pub struct Desugarer;

fn desugar_while(cond: Box<Expr>, body: Box<Expr>) -> Expr {
    Expr {
        span: body.span,
        ty: Type::unit(),
        // Make a while loop
        kind: ExprKind::Loop(Box::new(Expr {
            span: body.span,
            ty: body.ty,
            // With an if inside
            kind: ExprKind::If {
                else_: Some(Box::new(Expr {
                    kind: ExprKind::Break,
                    ty: Type::unit(),
                    span: cond.span,
                })),
                cond,
                // That only runs `body` if `cond` is true
                then_: body,
            },
        })),
    }
}

impl VisitMut for Desugarer {
    fn visit_texpr(&mut self, expr: &mut Expr) {
        // First recursively desugar children
        self.super_visit_texpr(expr);

        // Then desugar this expression
        match &mut expr.kind {
            #[allow(unused)]
            ExprKind::While { cond, body } => {
                // Desugar while loop to: loop { if cond { body } else { break } }
                *expr = desugar_while(cond.clone(), body.clone());
                // todo!("finish once break statements are implemented");
            }
            ExprKind::If { else_, .. } => {
                // Desugar if-without-else to if-else with unit else branch
                if else_.is_none() {
                    let unit_expr = Expr {
                        kind: ExprKind::Tuple(Vec::new()),
                        ty: Type::unit(),
                        span: expr.span,
                    };

                    *else_ = Some(Box::new(unit_expr));
                }
            }
            _ => {}
        }
    }
}

pub fn desugar(prog: &mut Program) {
    Desugarer.visit_program(prog);
}

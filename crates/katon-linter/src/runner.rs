use crate::context::LintContext;
use crate::lint::{Lint, LintDiagnostic, LintLevel};
use katon_core::ast::*;

pub struct Linter {
    lints: Vec<Box<dyn Lint>>,
}

impl Linter {
    pub fn new(lints: Vec<Box<dyn Lint>>) -> Self {
        Self { lints }
    }

    pub fn run_fn(&self, f: &FnDecl) -> Vec<LintDiagnostic> {
        let mut ctx = LintContext::default();
        let mut diags = Vec::new();

        for stmt in &f.body {
            self.visit_stmt(stmt, &mut ctx, &mut diags);
        }

        // Post-pass: unused variables
        for (id, span) in ctx.declared_vars {
            if !ctx.used_vars.contains(&id) {
                diags.push(LintDiagnostic {
                    code: "unused-variable",
                    message: "variable is never used".into(),
                    span,
                    level: LintLevel::Warning,
                });
            }
        }

        diags
    }

    fn visit_stmt(&self, stmt: &SStmt, ctx: &mut LintContext, diags: &mut Vec<LintDiagnostic>) {
        for lint in &self.lints {
            lint.check_stmt(stmt, ctx, diags);
        }

        match &stmt.node {
            Stmt::Let { value, .. } => {
                if let Some(expr) = value {
                    self.visit_expr(expr, ctx, diags);
                }
            }

            Stmt::Assign { value, .. } => {
                self.visit_expr(value, ctx, diags);
            }

            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                self.visit_expr(cond, ctx, diags);
                for s in then_block {
                    self.visit_stmt(s, ctx, diags);
                }
                for s in else_block {
                    self.visit_stmt(s, ctx, diags);
                }
            }

            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                self.visit_expr(cond, ctx, diags);
                self.visit_expr(invariant, ctx, diags);
                for s in body {
                    self.visit_stmt(s, ctx, diags);
                }
            }

            Stmt::ArrayUpdate { index, value, .. } => {
                self.visit_expr(index, ctx, diags);
                self.visit_expr(value, ctx, diags);
            }
        }
    }

    fn visit_expr(&self, expr: &SExpr, ctx: &mut LintContext, diags: &mut Vec<LintDiagnostic>) {
        for lint in &self.lints {
            lint.check_expr(expr, ctx, diags);
        }

        match &expr.node {
            Expr::Binary(lhs, _, rhs) => {
                self.visit_expr(lhs, ctx, diags);
                self.visit_expr(rhs, ctx, diags);
            }

            Expr::Cast(_, inner) => {
                self.visit_expr(inner, ctx, diags);
            }

            Expr::ArrayLit(elems) => {
                for e in elems {
                    self.visit_expr(e, ctx, diags);
                }
            }

            // Leaf expressions
            Expr::IntLit(_) | Expr::BoolLit(_) | Expr::Var(_, _) | Expr::Old(_, _) => {}
            _ => unimplemented!(),
        }
    }
}

use crate::ast::{Expr, FnDecl, Op, SExpr, SStmt, Stmt, Type};
use crate::errors::{CheckError, Diagnostic, Span};
use crate::symbol_table::TyCtx;

pub struct TypeChecker<'a> {
    tcx: &'a mut TyCtx,
}

impl<'a> TypeChecker<'a> {
    pub fn new(tcx: &'a mut TyCtx) -> Self {
        Self { tcx }
    }

    pub fn check_fn(&mut self, f: &FnDecl) -> Result<(), Diagnostic> {
        // params already have types
        for (id, ty) in &f.params {
            self.tcx.node_types.insert(*id, ty.clone());
        }

        for stmt in &f.body {
            self.check_stmt(stmt)?;
        }

        Ok(())
    }

    fn is_integer_type(&self, ty: &Type) -> bool {
        matches!(ty, Type::Int | Type::Nat)
    }

    fn check_if(
        &mut self,
        then_block: &[SStmt],
        else_block: &[SStmt],
        span: Span,
    ) -> Result<(), Diagnostic> {
        let snapshot = self.tcx.node_types.clone();

        self.check_block(then_block)?;
        let then_types = self.tcx.node_types.clone();

        self.tcx.node_types = snapshot.clone();
        self.check_block(else_block)?;
        let else_types = self.tcx.node_types.clone();

        // Only keep variables defined in BOTH branches
        self.tcx.node_types = snapshot;
        for (id, ty) in then_types {
            if let Some(ty2) = else_types.get(&id) {
                if ty == *ty2 {
                    self.tcx.node_types.insert(id, ty);
                } else {
                    return Err(Diagnostic {
                        error: CheckError::TypeMismatch {
                            expected: ty,
                            found: ty2.clone(),
                        },
                        span,
                    });
                }
            }
        }

        Ok(())
    }

    fn check_stmt(&mut self, stmt: &SStmt) -> Result<(), Diagnostic> {
        match &stmt.node {
            Stmt::Let { value, id, .. } => {
                let ty = self.check_expr(value)?;
                let id = id.expect("Resolver must assign ID");
                self.tcx.node_types.insert(id, ty);
                Ok(())
            }
            Stmt::Assign {
                value, target_id, ..
            } => {
                let rhs_ty = self.check_expr(value)?;
                let id = target_id.expect("Resolver must assign ID");

                let lhs_ty = self
                    .tcx
                    .node_types
                    .get(&id)
                    .cloned()
                    .ok_or(self.type_error("assign to untyped variable", stmt.span))?;

                if lhs_ty != rhs_ty {
                    return Err(Diagnostic {
                        error: CheckError::TypeMismatch {
                            expected: lhs_ty,
                            found: rhs_ty,
                        },
                        span: stmt.span,
                    });
                }
                Ok(())
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let cond_ty = self.check_expr(cond)?;
                if cond_ty != Type::Bool {
                    return Err(Diagnostic {
                        error: CheckError::TypeMismatch {
                            expected: Type::Bool,
                            found: cond_ty,
                        },
                        span: cond.span,
                    });
                }

                self.check_if(then_block, else_block, stmt.span)
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                if self.check_expr(cond)? != Type::Bool {
                    return Err(self.type_error("while condition must be Bool", cond.span));
                }
                if self.check_expr(invariant)? != Type::Bool {
                    return Err(self.type_error("loop invariant must be Bool", invariant.span));
                }

                for s in body {
                    self.check_stmt(s)?;
                }
                Ok(())
            }
            Stmt::ArrayUpdate {
                target_id,
                index,
                value,
                ..
            } => {
                let id = target_id.expect("Resolver must assign ID");

                let arr_ty = self
                    .tcx
                    .node_types
                    .get(&id)
                    .cloned()
                    .ok_or(self.type_error("update of untyped variable", stmt.span))?;

                let idx_ty = self.check_expr(index)?;

                if !self.is_integer_type(&idx_ty) {
                    return Err(self.type_error("array index must be Int or Nat", index.span));
                }

                let val_ty = self.check_expr(value)?;

                match arr_ty {
                    Type::Array(inner) if *inner == val_ty => Ok(()),
                    Type::Array(inner) => Err(Diagnostic {
                        error: CheckError::TypeMismatch {
                            expected: *inner,
                            found: val_ty,
                        },
                        span: stmt.span,
                    }),
                    other => Err(Diagnostic {
                        error: CheckError::InvalidIndex { base_ty: other },
                        span: stmt.span,
                    }),
                }
            }
        }
    }

    fn check_expr(&mut self, expr: &SExpr) -> Result<Type, Diagnostic> {
        let ty = match &expr.node {
            Expr::IntLit(_) => Type::Int,
            Expr::BoolLit(_) => Type::Bool,
            Expr::Var(name, id) | Expr::Old(name, id) => {
                let id = id.expect("Resolver assigned ID");

                if name.ends_with("_length") {
                    return Ok(Type::Int);
                }

                self.tcx
                    .node_types
                    .get(&id)
                    .cloned()
                    .ok_or(self.type_error("use of untyped variable", expr.span))?
            }
            Expr::Cast(ty, inner) => {
                let _ = self.check_expr(inner)?;
                ty.clone()
            }
            Expr::Binary(l, Op::Index, r) => {
                let idx_ty = self.check_expr(r)?;

                if !self.is_integer_type(&idx_ty) {
                    return Err(self.type_error("index must be Int or Nat", r.span));
                }

                match self.check_expr(l)? {
                    Type::Array(inner) => *inner,
                    other => {
                        return Err(Diagnostic {
                            error: CheckError::InvalidIndex { base_ty: other },
                            span: expr.span,
                        });
                    }
                }
            }
            Expr::Binary(l, op, r) => {
                let lt = self.check_expr(l)?;
                let rt = self.check_expr(r)?;

                if lt != rt {
                    return Err(Diagnostic {
                        error: CheckError::TypeMismatch {
                            expected: lt,
                            found: rt,
                        },
                        span: expr.span,
                    });
                }

                match op {
                    Op::Eq | Op::Neq | Op::Gt | Op::Lt | Op::Gte | Op::Lte => Type::Bool,
                    _ => lt,
                }
            }
        };

        Ok(ty)
    }

    fn check_block(&mut self, block: &[SStmt]) -> Result<(), Diagnostic> {
        for stmt in block {
            self.check_stmt(stmt)?;
        }
        Ok(())
    }

    fn type_error(&self, msg: &str, span: Span) -> Diagnostic {
        Diagnostic {
            error: CheckError::TypeError {
                msg: msg.to_string(),
            },
            span,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;

    fn checker() -> TypeChecker<'static> {
        let tcx = Box::leak(Box::new(TyCtx::default()));
        TypeChecker::new(tcx)
    }

    #[test]
    fn test_let_binding_typechecks() {
        let mut tc = checker();

        let stmt = SStmt {
            node: Stmt::Let {
                id: Some(NodeId(1)),
                name: "let".to_string(),
                value: SExpr {
                    node: Expr::IntLit(42),
                    span: Span::dummy(),
                },
            },
            span: Span::dummy(),
        };

        assert!(tc.check_stmt(&stmt).is_ok());
    }

    #[test]
    fn test_assignment_type_mismatch_fails() {
        let mut tc = checker();
        tc.tcx.node_types.insert(NodeId(1), Type::Int);

        let stmt = SStmt {
            node: Stmt::Assign {
                target: "=".to_string(),
                target_id: Some(NodeId(1)),
                value: SExpr {
                    node: Expr::BoolLit(true),
                    span: Span::dummy(),
                },
            },
            span: Span::dummy(),
        };

        let err = tc.check_stmt(&stmt).unwrap_err();
        assert!(matches!(err.error, CheckError::TypeMismatch { .. }));
    }

    #[test]
    fn test_if_requires_same_type_in_both_branches() {
        let mut tc = checker();

        let stmt = SStmt {
            node: Stmt::If {
                cond: SExpr {
                    node: Expr::BoolLit(true),
                    span: Span::dummy(),
                },
                then_block: vec![SStmt {
                    node: Stmt::Let {
                        id: Some(NodeId(1)),
                        name: "if".to_string(),
                        value: SExpr {
                            node: Expr::IntLit(1),
                            span: Span::dummy(),
                        },
                    },
                    span: Span::dummy(),
                }],
                else_block: vec![SStmt {
                    node: Stmt::Let {
                        id: Some(NodeId(1)),
                        name: "else".to_string(),
                        value: SExpr {
                            node: Expr::BoolLit(false),
                            span: Span::dummy(),
                        },
                    },
                    span: Span::dummy(),
                }],
            },
            span: Span::dummy(),
        };

        assert!(tc.check_stmt(&stmt).is_err());
    }

    #[test]
    fn while_invariant_must_be_bool() {
        let mut tc = checker();

        let stmt = SStmt {
            node: Stmt::While {
                cond: SExpr {
                    node: Expr::BoolLit(true),
                    span: Span::dummy(),
                },
                invariant: SExpr {
                    node: Expr::IntLit(1),
                    span: Span::dummy(),
                },
                body: vec![],
            },
            span: Span::dummy(),
        };

        assert!(tc.check_stmt(&stmt).is_err());
    }
}

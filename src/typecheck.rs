use crate::symbol_table::TyCtx;
use katon_core::Span;
use katon_core::ast::{Expr, FnDecl, Op, SExpr, SStmt, Stmt, Type};
use katon_core::errors::{CheckError, Diagnostic};

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

    fn check_compatibility(&self, expected: &Type, found: &Type) -> bool {
        if expected == found {
            return true;
        }

        // Allow assigning Int to Nat (Z3 will prove it's >= 0)
        if matches!(expected, Type::Nat) && matches!(found, Type::Int) {
            return true;
        }

        // Allow assigning Nat to Int
        if matches!(expected, Type::Int) && matches!(found, Type::Nat) {
            return true;
        }
        false
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
            Stmt::Let { ty, value, id, .. } => {
                let id = id.expect("Resolver must assign ID");

                match (ty, value) {
                    // let c: [int];
                    (Some(t), None) => {
                        self.tcx.insert_var(id, t.clone());
                    }

                    // let b = a;
                    (None, Some(expr)) => {
                        let t = self.check_expr(expr)?;
                        self.tcx.insert_var(id, t);
                    }

                    // let x: int = expr;
                    (Some(t), Some(expr)) => {
                        let expr_t = self.check_expr(expr)?;
                        if !self.check_compatibility(t, &expr_t) {
                            return Err(Diagnostic {
                                error: CheckError::TypeMismatch {
                                    expected: t.clone(),
                                    found: expr_t,
                                },
                                span: stmt.span,
                            });
                        }

                        self.tcx.insert_var(id, t.clone());
                    }

                    // impossible by grammar
                    (None, None) => unreachable!("parser prevents this"),
                }

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

                if !self.check_compatibility(&lhs_ty, &rhs_ty) {
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

                // Check if the target is actually an array and extract size/inner type
                let (arr_size, inner_ty) = match arr_ty {
                    Type::Array(size, inner) => (size, inner),
                    other => {
                        return Err(Diagnostic {
                            error: CheckError::InvalidIndex { base_ty: other },
                            span: stmt.span,
                        });
                    }
                };

                // Static Bound Checking
                match index.node {
                    Expr::IntLit(idx_val) if idx_val < 0 || idx_val as usize >= arr_size => {
                        return Err(self.type_error(
                            &format!(
                                "index {} out of bounds for array of size {}",
                                idx_val, arr_size
                            ),
                            index.span,
                        ));
                    }
                    _ => {} // Do nothing if it's not a literal or if it's in bounds
                }

                // Type consistency
                let val_ty = self.check_expr(value)?;
                if val_ty != *inner_ty {
                    return Err(Diagnostic {
                        error: CheckError::TypeMismatch {
                            expected: *inner_ty,
                            found: val_ty,
                        },
                        span: value.span,
                    });
                }

                Ok(())
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
                    Type::Array(size, inner) => {
                        // Static Bound Checking: If the index is a literal, check it now
                        match r.node {
                            Expr::IntLit(val) if val < 0 || (val as usize) >= size => {
                                return Err(self.type_error(
                                    &format!(
                                        "index {} is out of bounds for array of size {}",
                                        val, size
                                    ),
                                    r.span,
                                ));
                            }
                            _ => {}
                        }

                        *inner
                    }
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

                if self.is_integer_type(&lt) && self.is_integer_type(&rt) {
                    match op {
                        Op::Eq | Op::Neq | Op::Gt | Op::Lt | Op::Gte | Op::Lte => {
                            return Ok(Type::Bool);
                        }
                        _ => return Ok(Type::Int), // Math results in Int
                    }
                }

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
            Expr::ArrayLit(elems) => {
                if elems.is_empty() {
                    // Decide a default for empty literals, or enforce explicit typing
                    return Ok(Type::Array(0, Box::new(Type::Int)));
                }

                let first_ty = self.check_expr(&elems[0])?;
                for elem in elems.iter().skip(1) {
                    let ty = self.check_expr(elem)?;
                    if ty != first_ty {
                        return Err(Diagnostic {
                            error: CheckError::TypeMismatch {
                                expected: first_ty.clone(),
                                found: ty,
                            },
                            span: elem.span,
                        });
                    }
                }

                // Capture the ACTUAL length of the literal as part of the type
                Type::Array(elems.len(), Box::new(first_ty))
            }
            Expr::Borrow(inner) => self.check_expr(inner)?,
            Expr::Update { base, index, value } => {
                let base_ty = self.check_expr(base)?;

                match base_ty {
                    Type::Array(size, inner) => {
                        let idx = index.as_ref().expect("array update needs index");
                        let val = value.as_ref().expect("array update needs value");

                        let idx_ty = self.check_expr(idx)?;
                        if !self.is_integer_type(&idx_ty) {
                            return Err(self.type_error("index must be Int or Nat", idx.span));
                        }

                        let val_ty = self.check_expr(val)?;
                        if val_ty != *inner {
                            return Err(Diagnostic {
                                error: CheckError::TypeMismatch {
                                    expected: *inner,
                                    found: val_ty,
                                },
                                span: val.span,
                            });
                        }

                        // update(...) returns SAME array type
                        Type::Array(size, inner)
                    }

                    other => {
                        return Err(Diagnostic {
                            error: CheckError::InvalidIndex { base_ty: other },
                            span: expr.span,
                        });
                    }
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
    use katon_core::ast::*;

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
                ty: Some(Type::Int),
                name: "let".to_string(),
                value: Some(SExpr {
                    node: Expr::IntLit(42),
                    span: Span::dummy(),
                }),
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
                        ty: Some(Type::Int),
                        name: "if".to_string(),
                        value: Some(SExpr {
                            node: Expr::IntLit(1),
                            span: Span::dummy(),
                        }),
                    },
                    span: Span::dummy(),
                }],
                else_block: vec![SStmt {
                    node: Stmt::Let {
                        id: Some(NodeId(1)),
                        ty: Some(Type::Int),
                        name: "else".to_string(),
                        value: Some(SExpr {
                            node: Expr::BoolLit(false),
                            span: Span::dummy(),
                        }),
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

    #[test]
    fn test_borrow_preserves_type() {
        let mut tc = checker();
        tc.tcx.node_types.insert(NodeId(1), Type::Int);

        let expr = SExpr {
            node: Expr::Borrow(Box::new(SExpr {
                node: Expr::Var("x".to_string(), Some(NodeId(1))),
                span: Span::dummy(),
            })),
            span: Span::dummy(),
        };

        let ty = tc.check_expr(&expr).unwrap();
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn test_borrow_array_type() {
        let mut tc = checker();
        tc.tcx
            .node_types
            .insert(NodeId(1), Type::Array(4, Box::new(Type::Nat)));

        let expr = SExpr {
            node: Expr::Borrow(Box::new(SExpr {
                node: Expr::Var("arr".to_string(), Some(NodeId(1))),
                span: Span::dummy(),
            })),
            span: Span::dummy(),
        };

        let ty = tc.check_expr(&expr).unwrap();
        assert_eq!(ty, Type::Array(4, Box::new(Type::Nat)));
    }

    #[test]
    fn test_update_returns_same_array_type() {
        let mut tc = checker();
        tc.tcx
            .node_types
            .insert(NodeId(1), Type::Array(3, Box::new(Type::Int)));

        let expr = SExpr {
            node: Expr::Update {
                base: Box::new(SExpr {
                    node: Expr::Var("a".to_string(), Some(NodeId(1))),
                    span: Span::dummy(),
                }),
                index: Some(Box::new(SExpr {
                    node: Expr::IntLit(1),
                    span: Span::dummy(),
                })),
                value: Some(Box::new(SExpr {
                    node: Expr::IntLit(42),
                    span: Span::dummy(),
                })),
            },
            span: Span::dummy(),
        };

        let ty = tc.check_expr(&expr).unwrap();
        assert_eq!(ty, Type::Array(3, Box::new(Type::Int)));
    }

    #[test]
    fn test_update_non_array_fails() {
        let mut tc = checker();
        tc.tcx.node_types.insert(NodeId(1), Type::Int);

        let expr = SExpr {
            node: Expr::Update {
                base: Box::new(SExpr {
                    node: Expr::Var("x".to_string(), Some(NodeId(1))),
                    span: Span::dummy(),
                }),
                index: Some(Box::new(SExpr {
                    node: Expr::IntLit(0),
                    span: Span::dummy(),
                })),
                value: Some(Box::new(SExpr {
                    node: Expr::IntLit(1),
                    span: Span::dummy(),
                })),
            },
            span: Span::dummy(),
        };

        let err = tc.check_expr(&expr).unwrap_err();
        assert!(matches!(err.error, CheckError::InvalidIndex { .. }));
    }

    #[test]
    fn test_update_wrong_value_type_fails() {
        let mut tc = checker();
        tc.tcx
            .node_types
            .insert(NodeId(1), Type::Array(2, Box::new(Type::Bool)));

        let expr = SExpr {
            node: Expr::Update {
                base: Box::new(SExpr {
                    node: Expr::Var("a".to_string(), Some(NodeId(1))),
                    span: Span::dummy(),
                }),
                index: Some(Box::new(SExpr {
                    node: Expr::IntLit(0),
                    span: Span::dummy(),
                })),
                value: Some(Box::new(SExpr {
                    node: Expr::IntLit(1), // ❌ should be Bool
                    span: Span::dummy(),
                })),
            },
            span: Span::dummy(),
        };

        let err = tc.check_expr(&expr).unwrap_err();
        assert!(matches!(err.error, CheckError::TypeMismatch { .. }));
    }

    #[test]
    fn test_update_index_must_be_integer() {
        let mut tc = checker();
        tc.tcx
            .node_types
            .insert(NodeId(1), Type::Array(2, Box::new(Type::Int)));

        let expr = SExpr {
            node: Expr::Update {
                base: Box::new(SExpr {
                    node: Expr::Var("a".to_string(), Some(NodeId(1))),
                    span: Span::dummy(),
                }),
                index: Some(Box::new(SExpr {
                    node: Expr::BoolLit(true),
                    span: Span::dummy(),
                })),
                value: Some(Box::new(SExpr {
                    node: Expr::IntLit(0),
                    span: Span::dummy(),
                })),
            },
            span: Span::dummy(),
        };

        assert!(tc.check_expr(&expr).is_err());
    }
}

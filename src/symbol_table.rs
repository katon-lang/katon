use std::collections::HashMap;

use crate::{
    ast::{Expr, FnDecl, NodeId, SExpr, SStmt, Stmt, Type},
    errors::{CheckError, Diagnostic},
};

// Symbol table implementation to make the assignment know
// what data type is passing
// resolution: Maps a specific occurrence in code to a definition
// node_types: Maps a definition to its type
pub struct TyCtx {
    pub resolutions: HashMap<NodeId, Definition>,
    pub node_types: HashMap<NodeId, Type>,
}

impl Default for TyCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl TyCtx {
    pub fn new() -> Self {
        Self {
            resolutions: HashMap::new(),
            node_types: HashMap::new(),
        }
    }

    /// Get the type for a specific NodeId
    pub fn get_type(&self, id: &NodeId) -> Option<&Type> {
        self.node_types.get(id)
    }

    /// Helper for tests to register a variable type manually
    pub fn define_local(&mut self, id: NodeId, name: &str, ty: Type) {
        self.node_types.insert(id, ty);
        self.resolutions.insert(
            id,
            Definition {
                name: name.to_string(),
                kind: DefKind::Local,
            },
        );
    }

    pub fn insert_var(&mut self, id: NodeId, ty: Type) {
        self.node_types.insert(id, ty);
    }

    /// Look up the original String name for a given NodeId.
    /// Returns a fallback string if the ID is missing (useful for debugging).
    pub fn get_name(&self, id: &NodeId) -> String {
        self.resolutions
            .get(id)
            .map(|def| def.name.clone())
            .unwrap_or_else(|| format!("var_{}", id.0))
    }
}

pub struct Definition {
    pub name: String,
    pub kind: DefKind,
}

pub enum DefKind {
    Local,
    Param,
    Function,
}

// Resolver
// turn ambiguous strings into specific, unique identities
pub struct Resolver {
    scopes: Vec<HashMap<String, NodeId>>, // A stack of scopes: name -> unique ID
    next_id: u32,
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}

impl Resolver {
    pub fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            next_id: 0,
        }
    }

    pub fn resolve_stmt(&mut self, stmt: &mut SStmt) -> Result<(), Diagnostic> {
        match &mut stmt.node {
            Stmt::Assign {
                target,
                target_id,
                value,
            } => {
                // Resolve the RHS first (e.g., y = x + 1)
                self.resolve_expr(value).map_err(|msg| Diagnostic {
                    error: CheckError::UndefinedVariable {
                        var: msg.to_string(),
                    },
                    span: stmt.span,
                })?;

                // Resolve the LHS
                // If it's already in scope, use that ID
                // Make assignment require prior definition
                // Must declare the variable with `let`
                if let Some(id) = self.resolve(target) {
                    *target_id = Some(id);
                } else {
                    return Err(Diagnostic {
                        error: CheckError::UndefinedVariable {
                            var: target.to_string(),
                        },
                        span: stmt.span,
                    });
                }
            }
            Stmt::Let {
                name, value, id, ..
            } => {
                if let Some(expr) = value {
                    self.resolve_expr(expr)?;
                }

                // 2. Create the unique NodeId for this variable
                let new_id = self.define(name.clone());
                *id = Some(new_id);
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                self.resolve_expr(cond)?;

                self.enter_scope();
                for s in then_block {
                    self.resolve_stmt(s)?;
                }
                self.exit_scope();

                self.enter_scope();
                for s in else_block {
                    self.resolve_stmt(s)?;
                }
                self.exit_scope();
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                self.resolve_expr(cond)?;
                self.resolve_expr(invariant)?;

                self.enter_scope();
                for s in body {
                    self.resolve_stmt(s)?;
                }

                self.exit_scope();
            }
            Stmt::ArrayUpdate {
                target,
                target_id,
                index,
                value,
            } => {
                self.resolve_expr(index)?;
                self.resolve_expr(value)?;

                if let Some(id) = self.resolve(target) {
                    *target_id = Some(id);
                } else {
                    return Err(Diagnostic {
                        error: CheckError::UndefinedArray {
                            var: target.clone(),
                        },
                        span: stmt.span,
                    });
                }
            }
        }

        Ok(())
    }

    pub fn resolve_expr(&mut self, expr: &mut SExpr) -> Result<(), Diagnostic> {
        match &mut expr.node {
            Expr::Var(name, id_slot) => {
                if let Some(id) = self.resolve(name) {
                    *id_slot = Some(id);
                    Ok(())
                } else if name.ends_with("_length") {
                    let base_name = &name[..name.len() - 7];
                    if let Some(id) = self.resolve(base_name) {
                        *id_slot = Some(id);
                        Ok(())
                    } else {
                        Err(Diagnostic {
                            error: CheckError::UndefinedVariable { var: name.clone() },
                            span: expr.span,
                        })
                    }
                } else {
                    Err(Diagnostic {
                        error: CheckError::UndefinedVariable { var: name.clone() },
                        span: expr.span,
                    })
                }
            }
            Expr::Binary(lhs, _, rhs) => {
                self.resolve_expr(lhs)?;
                self.resolve_expr(rhs)
            }
            Expr::Cast(_ty, inner) => self.resolve_expr(inner),
            Expr::Old(name, id_slot) => {
                if let Some(id) = self.resolve(name) {
                    *id_slot = Some(id);
                    Ok(())
                } else {
                    Err(Diagnostic {
                        error: CheckError::UndefinedVariable { var: name.clone() },
                        span: expr.span,
                    })
                }
            }
            _ => Ok(()),
        }
    }

    pub fn resolve_function(
        &mut self,
        func: &mut FnDecl,
        tcx: &mut TyCtx,
    ) -> Result<(), Diagnostic> {
        self.enter_scope();

        // 1. Synchronize Names to Real IDs
        let mut resolved_params = Vec::new();

        // We pair the temporary params with the actual names we saved
        for (i, name) in func.param_names.iter().enumerate() {
            let ty = func.params[i].1.clone();

            // Generate a REAL unique ID
            let id = self.define(name.clone());

            // Register in Symbol Table
            tcx.node_types.insert(id, ty.clone());
            tcx.resolutions.insert(
                id,
                Definition {
                    name: name.clone(),
                    kind: DefKind::Param,
                },
            );

            resolved_params.push((id, ty));
        }

        // 2. Overwrite the dummy params with the real ones
        func.params = resolved_params;

        // 3. Proceed with the rest of the resolution
        for req in &mut func.requires {
            self.resolve_expr(req)?;
        }
        for stmt in &mut func.body {
            self.resolve_stmt(stmt)?;
        }
        for ens in &mut func.ensures {
            self.resolve_expr(ens)?;
        }

        self.exit_scope();
        Ok(())
    }

    fn generate_id(&mut self) -> NodeId {
        let id = NodeId(self.next_id);
        self.next_id += 1;
        id
    }

    // Enter a new lexical scope
    fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    // Exit the current lexical scope
    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    // Define a new name in the current (innermost) scope
    fn define(&mut self, name: String) -> NodeId {
        let id = self.generate_id();
        if let Some(current) = self.scopes.last_mut() {
            current.insert(name, id);
        }

        id
    }

    // Look up a name starting from the innermost scope (handles shadowing)
    fn resolve(&self, name: &str) -> Option<NodeId> {
        for scope in self.scopes.iter().rev() {
            if let Some(id) = scope.get(name) {
                return Some(*id);
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, SExpr, Type};
    use crate::errors::Span;

    fn dummy_span() -> Span {
        Span { start: 0, end: 0 }
    }

    #[test]
    fn test_basic_resolution_and_shadowing() {
        let mut resolver = Resolver::new();
        let mut tcx = TyCtx::new();

        // 1. Define 'x' in global/outer scope
        let id_x_outer = resolver.define("x".to_string());
        tcx.define_local(id_x_outer, "x", Type::Int);

        // 2. Enter a new scope and shadow 'x'
        resolver.enter_scope();
        let id_x_inner = resolver.define("x".to_string());
        tcx.define_local(id_x_inner, "x", Type::Bool);

        // Verify that in the current scope, 'x' resolves to the inner ID
        let resolved_id = resolver.resolve("x").expect("Should find x");
        assert_eq!(resolved_id, id_x_inner);
        assert_eq!(tcx.get_type(&resolved_id), Some(&Type::Bool));

        // 3. Exit scope and verify 'x' resolves to the outer ID again
        resolver.exit_scope();
        let resolved_id_back = resolver.resolve("x").expect("Should find x");
        assert_eq!(resolved_id_back, id_x_outer);
        assert_eq!(tcx.get_type(&resolved_id_back), Some(&Type::Int));
    }

    #[test]
    fn test_resolve_expr_variable() {
        let mut resolver = Resolver::new();
        let var_name = "my_var".to_string();
        let expected_id = resolver.define(var_name.clone());

        // Create an Expr::Var with an empty NodeId slot
        let mut expr = SExpr {
            node: Expr::Var(var_name.clone(), None),
            span: dummy_span(),
        };

        // Run resolution
        resolver.resolve_expr(&mut expr).expect("Resolution failed");

        // Check if the ID was correctly injected into the AST node
        if let Expr::Var(_, Some(actual_id)) = expr.node {
            assert_eq!(actual_id, expected_id);
        } else {
            panic!("NodeId was not populated in Expr::Var");
        }
    }

    #[test]
    fn test_undefined_variable_error() {
        let mut resolver = Resolver::new();
        let mut expr = SExpr {
            node: Expr::Var("ghost".to_string(), None),
            span: dummy_span(),
        };

        let result = resolver.resolve_expr(&mut expr);
        assert!(
            result.is_err(),
            "Should return error for undefined variable"
        );
    }

    #[test]
    fn test_array_length_magic_resolution() {
        let mut resolver = Resolver::new();
        let arr_name = "my_array".to_string();
        let arr_id = resolver.define(arr_name);

        // Try to resolve "my_array_length"
        let mut expr = SExpr {
            node: Expr::Var("my_array_length".to_string(), None),
            span: dummy_span(),
        };

        resolver
            .resolve_expr(&mut expr)
            .expect("Should resolve _length suffix");

        if let Expr::Var(_, Some(actual_id)) = expr.node {
            assert_eq!(
                actual_id, arr_id,
                "Array length should map to the array's NodeId"
            );
        } else {
            panic!("NodeId was not populated for array length");
        }
    }
}

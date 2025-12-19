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
                // 1. Resolve the RHS first (e.g., y = x + 1)
                self.resolve_expr(value).map_err(|msg| Diagnostic {
                    error: CheckError::UndefinedVariable {
                        var: msg.to_string(),
                    },
                    span: stmt.span,
                })?;

                // 2. Resolve the LHS
                // If it's already in scope, use that ID. If not, define it.
                if let Some(id) = self.resolve(target) {
                    *target_id = Some(id);
                } else {
                    let new_id = self.define(target.clone());
                    *target_id = Some(new_id);
                }
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

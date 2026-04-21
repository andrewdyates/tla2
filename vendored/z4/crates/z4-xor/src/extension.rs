// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! XOR theory extension for SAT solver integration.

use z4_sat::{ExtCheckResult, ExtPropagateResult, Extension, Literal, SolverContext, Variable};

use crate::constraint::XorConstraint;
use crate::gaussian::{GaussResult, GaussianSolver};
use crate::VarId;

/// An assignment record for backtracking.
#[derive(Debug, Clone)]
struct AssignmentRecord {
    /// The variable that was assigned.
    var: VarId,
    /// The decision level at which the assignment was made.
    level: u32,
}

/// A pending propagation with its source RREF row.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PendingPropagation {
    /// The literal to propagate.
    lit: Literal,
    /// The RREF row index that caused this propagation.
    /// Used to build minimal reason clauses.
    source_row: usize,
}

/// XOR theory extension for SAT solver integration.
///
/// This implements the `Extension` trait to integrate Gauss-Jordan XOR solving
/// with the SAT solver. It tracks assignments, detects conflicts and unit
/// propagations, and supports backtracking.
///
/// # Usage
///
/// ```rust
/// use z4_xor::{XorConstraint, XorExtension};
///
/// // Create XOR constraints
/// let constraints = vec![
///     XorConstraint::new(vec![0, 1], true),  // x0 XOR x1 = 1
///     XorConstraint::new(vec![1, 2], false), // x1 XOR x2 = 0
/// ];
///
/// // Create extension
/// let ext = XorExtension::new(constraints);
///
/// // Add to SAT solver (solver.set_extension(ext))
/// ```
#[derive(Debug)]
pub struct XorExtension {
    /// The underlying Gaussian elimination solver.
    solver: GaussianSolver,
    /// Original constraints (needed for backtracking/rebuild).
    constraints: Vec<XorConstraint>,
    /// Trail of assignments with their levels (for backtracking).
    trail: Vec<AssignmentRecord>,
    /// Last trail position we processed.
    last_trail_pos: usize,
    /// Pending propagations (unit literals found by Gauss) with source row.
    pub(crate) pending_propagations: Vec<PendingPropagation>,
    /// Current conflict (if any) with source row index.
    pub(crate) conflict: Option<(Vec<Literal>, Option<usize>)>,
    /// Whether we need to propagate.
    pub(crate) needs_propagate: bool,
    /// Whether the tracked assignment state must be rebuilt from the SAT trail.
    needs_resync: bool,
    /// Debug counter: propagate calls.
    #[cfg(debug_assertions)]
    debug_propagate_calls: std::cell::Cell<u64>,
    /// Debug counter: backtrack calls.
    #[cfg(debug_assertions)]
    debug_backtrack_calls: std::cell::Cell<u64>,
}

impl XorExtension {
    /// Create a new XOR extension with the given constraints.
    pub fn new(constraints: Vec<XorConstraint>) -> Self {
        let mut solver = GaussianSolver::new(&constraints);

        // Initial elimination
        let result = solver.eliminate();

        // Check for initial conflict (constraints are inconsistent)
        let conflict = match result {
            GaussResult::Conflict(row_idx) => {
                // Build conflict clause from the conflicting row's variables
                let clause: Vec<Literal> = solver
                    .get_row_variables(row_idx)
                    .into_iter()
                    .map(|(var_id, _col)| Literal::positive(Variable::new(var_id)))
                    .collect();
                Some((clause, Some(row_idx)))
            }
            _ => None,
        };

        // Get initial propagations (units from RREF)
        let initial_props: Vec<PendingPropagation> = solver
            .get_all_propagations()
            .into_iter()
            .map(|(lit, source_row)| PendingPropagation { lit, source_row })
            .collect();

        let needs_propagate = !initial_props.is_empty() || conflict.is_some();

        Self {
            solver,
            constraints,
            trail: Vec::new(),
            last_trail_pos: 0,
            pending_propagations: initial_props,
            conflict,
            needs_propagate,
            needs_resync: false,
            #[cfg(debug_assertions)]
            debug_propagate_calls: std::cell::Cell::new(0),
            #[cfg(debug_assertions)]
            debug_backtrack_calls: std::cell::Cell::new(0),
        }
    }

    /// Get the number of XOR constraints.
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Get the number of variables in XOR constraints.
    pub fn num_variables(&self) -> usize {
        self.solver.num_variables()
    }

    /// Check if a variable is in any XOR constraint.
    pub fn contains_var(&self, var: VarId) -> bool {
        self.solver.has_variable(var)
    }

    /// Get the original XOR constraints.
    pub fn constraints(&self) -> &[XorConstraint] {
        &self.constraints
    }

    /// Build a conflict clause from a specific RREF row.
    ///
    /// Uses only the variables in the source row that caused the conflict,
    /// not the entire trail. This produces minimal conflict clauses.
    fn build_conflict_clause_from_row(&self, row_idx: usize) -> Vec<Literal> {
        self.solver
            .get_row_variables(row_idx)
            .into_iter()
            .filter_map(|(var_id, col)| {
                // Only include assigned variables
                if let Some(value) = self.solver.assignment_at(col) {
                    let var = Variable::new(var_id);
                    // Negate the assignment
                    Some(if value {
                        Literal::negative(var)
                    } else {
                        Literal::positive(var)
                    })
                } else {
                    None
                }
            })
            .collect()
    }

    /// Build a reason clause for a propagated literal from a specific RREF row.
    ///
    /// The propagated literal is stored first to satisfy
    /// `add_theory_propagation()`'s reason-clause layout.
    fn build_propagation_clause_from_row(
        &self,
        propagated: Literal,
        row_idx: usize,
    ) -> Option<Vec<Literal>> {
        let row_vars = self.solver.get_row_variables(row_idx);
        let mut clause = Vec::with_capacity(row_vars.len());
        clause.push(propagated);

        for (var_id, col) in row_vars {
            if var_id == propagated.variable().id() {
                continue;
            }

            let value = self.solver.assignment_at(col)?;
            let var = Variable::new(var_id);
            clause.push(if value {
                Literal::negative(var)
            } else {
                Literal::positive(var)
            });
        }

        Some(clause)
    }

    /// Record propagation/conflict information produced by the Gaussian solver.
    ///
    /// Returns `true` if a conflict was found and processing should stop.
    fn record_gauss_result(&mut self, result: GaussResult, ctx: &dyn SolverContext) -> bool {
        match result {
            GaussResult::Conflict(row_idx) => {
                let conflict = self.build_conflict_clause_from_row(row_idx);
                self.conflict = Some((conflict, Some(row_idx)));
                self.needs_propagate = true;
                self.last_trail_pos = ctx.trail().len();
                true
            }
            GaussResult::Propagate(prop_lit, source_row) => {
                if ctx.value(prop_lit.variable()).is_none() {
                    self.pending_propagations.push(PendingPropagation {
                        lit: prop_lit,
                        source_row,
                    });
                }
                false
            }
            GaussResult::MultiPropagate(props) => {
                for (prop_lit, source_row) in props {
                    if ctx.value(prop_lit.variable()).is_none() {
                        self.pending_propagations.push(PendingPropagation {
                            lit: prop_lit,
                            source_row,
                        });
                    }
                }
                false
            }
            GaussResult::Nothing => false,
        }
    }

    /// Rebuild tracked assignments and pending state from the SAT trail.
    fn rebuild_from_context(&mut self, ctx: &dyn SolverContext) {
        self.solver.clear_assignments();
        self.trail.clear();
        self.pending_propagations.clear();
        self.conflict = None;
        self.last_trail_pos = 0;

        let current_level = ctx.decision_level();
        for &lit in ctx.trail() {
            let var = lit.variable();
            let var_id = var.id();
            if !self.solver.has_variable(var_id) {
                continue;
            }

            let level = ctx.var_level(var).unwrap_or(current_level);
            self.trail.push(AssignmentRecord { var: var_id, level });
            let _ = self.solver.assign(var_id, lit.is_positive());
        }

        self.pending_propagations = self
            .solver
            .get_all_propagations()
            .into_iter()
            .filter(|(lit, _)| ctx.value(lit.variable()).is_none())
            .map(|(lit, source_row)| PendingPropagation { lit, source_row })
            .collect();
        self.conflict = self
            .solver
            .find_conflict_row()
            .map(|row_idx| (self.build_conflict_clause_from_row(row_idx), Some(row_idx)));
        self.last_trail_pos = ctx.trail().len();
        self.needs_resync = false;
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }

    /// Synchronize the XOR solver with the SAT trail.
    fn sync_with_context(&mut self, ctx: &dyn SolverContext) {
        if self.needs_resync || self.last_trail_pos > ctx.trail().len() {
            self.rebuild_from_context(ctx);
        } else {
            self.process_assignments(ctx);
        }
    }

    /// Process new assignments and update the solver.
    fn process_assignments(&mut self, ctx: &dyn SolverContext) {
        let new_lits = ctx.new_assignments(self.last_trail_pos);
        let current_level = ctx.decision_level();

        for &lit in new_lits {
            let var = lit.variable();
            let var_id = var.id();

            // Only process variables that are in XOR constraints
            if !self.solver.has_variable(var_id) {
                continue;
            }

            // Record the assignment for backtracking
            let level = ctx.var_level(var).unwrap_or(current_level);
            self.trail.push(AssignmentRecord { var: var_id, level });

            // Assign in the Gaussian solver
            let value = lit.is_positive();
            let result = self.solver.assign(var_id, value);
            if self.record_gauss_result(result, ctx) {
                return;
            }
        }

        self.last_trail_pos = ctx.trail().len();
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }
}

impl Extension for XorExtension {
    fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
        #[cfg(debug_assertions)]
        self.debug_propagate_calls
            .set(self.debug_propagate_calls.get() + 1);

        self.sync_with_context(ctx);

        // Conflicts take priority over unit propagations.
        if let Some((conflict, _row_idx)) = self.conflict.take() {
            self.needs_propagate = self.needs_resync || !self.pending_propagations.is_empty();
            return ExtPropagateResult::conflict(conflict);
        }

        if !self.pending_propagations.is_empty() {
            let mut propagations = Vec::new();
            let mut malformed_reason = false;
            let pending = std::mem::take(&mut self.pending_propagations);

            for prop in pending {
                if ctx.value(prop.lit.variable()).is_some() {
                    continue;
                }

                if let Some(clause) =
                    self.build_propagation_clause_from_row(prop.lit, prop.source_row)
                {
                    propagations.push((clause, prop.lit));
                } else {
                    malformed_reason = true;
                    debug_assert!(
                        false,
                        "pending XOR propagation for row {} was not unit under current assignments",
                        prop.source_row
                    );
                }
            }

            self.needs_resync = malformed_reason;
            self.needs_propagate = malformed_reason;
            if !propagations.is_empty() {
                return ExtPropagateResult::new(vec![], propagations, None, false);
            }
        }

        self.needs_propagate = self.needs_resync;
        ExtPropagateResult::none()
    }

    fn asserted(&mut self, _lit: Literal) {
        // We handle assignments in propagate() via new_assignments()
        // Mark that we need to check for propagations
        self.needs_propagate = true;
    }

    fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
        self.sync_with_context(ctx);

        if let Some((conflict, _row_idx)) = &self.conflict {
            return ExtCheckResult::Conflict(conflict.clone());
        }

        // Final soundness check: verify the original XOR constraints directly
        // against the SAT solver's model.
        for constraint in &self.constraints {
            let mut parity = false;
            for &var in &constraint.vars {
                let value = ctx.value(Variable::new(var)).unwrap_or(false);
                parity ^= value;
            }
            if parity != constraint.rhs {
                // Constraint violated - build conflict clause
                let conflict: Vec<Literal> = constraint
                    .vars
                    .iter()
                    .map(|&var| {
                        let value = ctx.value(Variable::new(var)).unwrap_or(false);
                        if value {
                            Literal::negative(Variable::new(var))
                        } else {
                            Literal::positive(Variable::new(var))
                        }
                    })
                    .collect();
                return ExtCheckResult::Conflict(conflict);
            }
        }

        ExtCheckResult::Sat
    }

    fn backtrack(&mut self, new_level: u32) {
        #[cfg(debug_assertions)]
        self.debug_backtrack_calls
            .set(self.debug_backtrack_calls.get() + 1);

        // Pop assignments from our trail and unassign in solver.
        while let Some(rec) = self.trail.last() {
            if rec.level <= new_level {
                break;
            }
            let rec = self
                .trail
                .pop()
                .expect("trail.last() returned Some, pop must succeed");
            self.solver.unassign(rec.var);
        }

        // Recompute propagation state from the full RREF after backtrack.
        // Rows can become unit because a non-watched variable was unassigned,
        // so checking only the affected watch lists is incomplete.
        self.pending_propagations.clear();
        self.conflict = None;

        // Reset satisfied_rows - watches remain valid after backtrack
        self.solver.reset_satisfied();
        self.needs_resync = true;
        self.needs_propagate = true;
    }

    fn init(&mut self) {
        self.solver.clear_assignments();
        self.trail.clear();
        self.last_trail_pos = 0;

        // Get initial propagations
        self.pending_propagations = self
            .solver
            .get_all_propagations()
            .into_iter()
            .map(|(lit, source_row)| PendingPropagation { lit, source_row })
            .collect();
        // Check for initial conflict and build minimal clause from specific row
        self.conflict = self
            .solver
            .find_conflict_row()
            .map(|row| (self.build_conflict_clause_from_row(row), Some(row)));
        self.needs_resync = false;
        self.needs_propagate = !self.pending_propagations.is_empty() || self.conflict.is_some();
    }

    fn can_propagate(&self, ctx: &dyn SolverContext) -> bool {
        // Check if there are pending XOR propagations OR new SAT assignments
        // since our last propagate() call that we need to process.
        //
        // This is O(1) and avoids the overhead of always calling propagate().
        self.needs_resync || self.needs_propagate || ctx.trail().len() != self.last_trail_pos
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Gauss-Jordan elimination solver for XOR constraints.

use hashbrown::HashMap;
use z4_sat::{Literal, Variable};

use crate::constraint::XorConstraint;
use crate::packed_row::{PackedRow, RowState};
use crate::VarId;

/// Result of a Gaussian elimination step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GaussResult {
    /// No propagation or conflict.
    Nothing,
    /// A variable can be propagated (unit constraint found).
    /// Contains the propagated literal and the source RREF row index.
    Propagate(Literal, usize),
    /// Multiple variables can be propagated (multiple unit constraints found).
    /// Contains all propagated literals with their source RREF row indices.
    /// This is more efficient than returning one at a time.
    MultiPropagate(Vec<(Literal, usize)>),
    /// A conflict was detected (0 = 1).
    /// Contains the source RREF row index.
    Conflict(usize),
}

/// Gauss-Jordan elimination solver for XOR constraints.
///
/// Maintains a matrix in reduced row echelon form and supports incremental
/// updates when variables are assigned.
///
/// # Incremental Backtracking
///
/// The solver stores the initial RREF matrix separately from the working copy.
/// On backtrack, we copy the RREF rows back instead of re-eliminating from
/// scratch, reducing backtrack cost from O(n×m×k) to O(n×m).
#[derive(Debug)]
pub struct GaussianSolver {
    /// Matrix rows (working copy, modified by assignments).
    pub(crate) rows: Vec<PackedRow>,
    /// Initial RREF matrix (computed once, used for fast backtrack restore).
    pub(crate) rref_rows: Vec<PackedRow>,
    /// Initial RREF right-hand sides (stored separately for fast restore).
    rref_rhs: Vec<bool>,
    /// Variable to column mapping.
    pub(crate) var_to_col: HashMap<VarId, usize>,
    /// Column to variable mapping.
    col_to_var: Vec<VarId>,
    /// Which row is responsible for each column (pivot row).
    /// None means no row has this column as pivot.
    col_to_pivot_row: Vec<Option<usize>>,
    /// Initial pivot mapping (for fast restore).
    rref_col_to_pivot_row: Vec<Option<usize>>,
    /// Number of variables/columns.
    num_cols: usize,
    /// Current variable assignments (None = unassigned).
    pub(crate) assignments: Vec<Option<bool>>,
    /// Packed columns assigned to true.
    assigned_true_cols: PackedRow,
    /// Packed columns that are currently unassigned.
    unassigned_cols: PackedRow,
    /// Watched constraints: for each column, list of rows watching it.
    /// A row watches columns with non-zero coefficients where we expect propagations.
    watches: Vec<Vec<usize>>,
    /// For each row: indices of the two watched columns [watch0, watch1].
    /// None means no watch (row may be all-zero or satisfied).
    row_watches: Vec<[Option<usize>; 2]>,
    /// Rows that are currently satisfied (all variables assigned, parity matches).
    satisfied_rows: Vec<bool>,
}

impl GaussianSolver {
    /// Create a new solver with the given XOR constraints.
    pub fn new(constraints: &[XorConstraint]) -> Self {
        // Collect all variables
        let mut all_vars: Vec<VarId> = constraints
            .iter()
            .flat_map(|c| c.vars.iter().copied())
            .collect();
        all_vars.sort_unstable();
        all_vars.dedup();

        let num_cols = all_vars.len();
        let num_rows = constraints.len();

        // Build mappings
        let var_to_col: HashMap<VarId, usize> = all_vars
            .iter()
            .enumerate()
            .map(|(col, &var)| (var, col))
            .collect();
        let col_to_var = all_vars;

        // Build matrix rows
        let rows: Vec<PackedRow> = constraints
            .iter()
            .map(|c| PackedRow::from_xor(c, &var_to_col, num_cols))
            .collect();
        let assigned_true_cols = PackedRow::new(num_cols);
        let mut unassigned_cols = PackedRow::new(num_cols);
        unassigned_cols.fill_ones();

        Self {
            rows,
            // RREF state initialized empty, filled by eliminate()
            rref_rows: Vec::with_capacity(num_rows),
            rref_rhs: Vec::with_capacity(num_rows),
            var_to_col,
            col_to_var,
            col_to_pivot_row: vec![None; num_cols],
            rref_col_to_pivot_row: vec![None; num_cols],
            num_cols,
            assignments: vec![None; num_cols],
            assigned_true_cols,
            unassigned_cols,
            // Watch structures initialized empty, filled by init_watches() after eliminate()
            watches: vec![Vec::new(); num_cols],
            row_watches: vec![[None, None]; num_rows],
            satisfied_rows: vec![false; num_rows],
        }
    }

    /// Perform full Gauss-Jordan elimination.
    ///
    /// After this, the matrix is in reduced row echelon form.
    /// Also saves the RREF state for fast backtrack restoration.
    /// Returns `GaussResult::Conflict` if a conflict is found.
    pub fn eliminate(&mut self) -> GaussResult {
        let num_rows = self.rows.len();
        let mut pivot_row_idx = 0;

        for col in 0..self.num_cols {
            // Find pivot: first row with "1" in this column (at or below pivot_row_idx)
            let mut found_pivot = None;
            for row_idx in pivot_row_idx..num_rows {
                if self.rows[row_idx].get(col) {
                    found_pivot = Some(row_idx);
                    break;
                }
            }

            if let Some(pivot_idx) = found_pivot {
                // Swap pivot row to current position
                if pivot_idx != pivot_row_idx {
                    self.rows.swap(pivot_idx, pivot_row_idx);
                }

                // Record that this column has a pivot
                self.col_to_pivot_row[col] = Some(pivot_row_idx);

                // XOR pivot into ALL other rows with "1" in this column
                // This is Gauss-Jordan (eliminates above AND below)
                for row_idx in 0..num_rows {
                    if row_idx != pivot_row_idx && self.rows[row_idx].get(col) {
                        // Need to clone to satisfy borrow checker
                        let pivot_row = self.rows[pivot_row_idx].clone();
                        self.rows[row_idx].xor_in(&pivot_row);
                    }
                }

                pivot_row_idx += 1;
            }
        }

        // Save RREF state for fast backtrack restoration
        // This is O(n*m) but only done once after initial elimination
        // We save BEFORE checking for conflicts so restore_rref() works even on conflict
        self.rref_rows = self.rows.clone();
        self.rref_rhs = self.rows.iter().map(|r| r.rhs).collect();
        self.rref_col_to_pivot_row = self.col_to_pivot_row.clone();

        // Initialize watched constraints for efficient propagation
        self.init_watches();

        // Check for conflicts (all-zero row with non-zero RHS)
        for (row_idx, row) in self.rows.iter().enumerate() {
            if row.is_zero() && row.rhs {
                return GaussResult::Conflict(row_idx);
            }
        }

        GaussResult::Nothing
    }

    /// Get the active matrix rows (RREF if available, raw otherwise).
    #[inline]
    fn active_rows(&self) -> &[PackedRow] {
        if self.rref_rows.is_empty() {
            &self.rows
        } else {
            &self.rref_rows
        }
    }

    /// Evaluate a row against the current packed assignment state.
    #[inline]
    fn evaluate_row(&self, row: &PackedRow) -> RowState {
        row.evaluate_with_column_state(&self.assigned_true_cols, &self.unassigned_cols)
    }

    /// Update the packed column state for a single assignment change.
    #[inline]
    fn set_assignment_state(&mut self, col: usize, value: Option<bool>) {
        self.unassigned_cols.set(col, value.is_none());
        self.assigned_true_cols.set(col, value == Some(true));
    }

    /// Initialize watched constraints after elimination.
    ///
    /// Each non-trivial row watches exactly 2 columns (variables). When a watched
    /// variable is assigned, we check if the row becomes unit or conflict. This
    /// gives O(watching_rows * num_cols) worst-case per assignment instead of
    /// O(n*m) per assignment. Amortized cost depends on watch movement frequency.
    fn init_watches(&mut self) {
        // Clear any existing watches
        for watches in &mut self.watches {
            watches.clear();
        }
        for row_watch in &mut self.row_watches {
            *row_watch = [None, None];
        }
        for sat in &mut self.satisfied_rows {
            *sat = false;
        }

        // For each row, find first 2 non-zero columns and watch them
        // Note: can't use active_rows() here because the loop body mutates
        // self.watches and self.row_watches (split borrow).
        let rows = if self.rref_rows.is_empty() {
            &self.rows
        } else {
            &self.rref_rows
        };
        for (row_idx, row) in rows.iter().enumerate() {
            let mut watch_count = 0;
            for col in 0..self.num_cols {
                if row.get(col) {
                    // This column has a 1 in this row - watch it
                    self.watches[col].push(row_idx);
                    self.row_watches[row_idx][watch_count] = Some(col);
                    watch_count += 1;
                    if watch_count == 2 {
                        break;
                    }
                }
            }
        }
    }

    /// Assign a variable and propagate using watched constraints.
    ///
    /// Returns propagation or conflict information. Uses watched constraints
    /// to avoid scanning all rows. Per-assignment cost is O(watching_rows * num_cols)
    /// worst-case when watches need replacement; O(watching_rows) when they don't.
    pub fn assign(&mut self, var: VarId, value: bool) -> GaussResult {
        let Some(&col) = self.var_to_col.get(&var) else {
            return GaussResult::Nothing; // Variable not in any XOR
        };

        debug_assert!(
            self.assignments[col].is_none() || self.assignments[col] == Some(value),
            "reassigning XOR variable {} from {:?} to {}",
            var,
            self.assignments[col],
            value,
        );
        self.assignments[col] = Some(value);
        self.set_assignment_state(col, Some(value));

        // Use watched propagation for efficiency
        self.propagate_watched(col)
    }

    /// Propagate using watched constraints.
    ///
    /// When a watched variable is assigned, we examine only the rows watching
    /// that variable. For each row:
    /// - If satisfied, skip
    /// - If conflict (0 unassigned, parity mismatch), return conflict
    /// - If unit (1 unassigned), collect propagation (continue to find more)
    /// - If 2+ unassigned, try to find a new watch
    ///
    /// Returns all propagations found in a single pass. This is more efficient
    /// than returning one at a time because it reduces solver round-trips.
    fn propagate_watched(&mut self, assigned_col: usize) -> GaussResult {
        // Take the watch list for this column (we'll rebuild it)
        let watching_rows = std::mem::take(&mut self.watches[assigned_col]);

        // Collect updates to apply after the immutable borrow phase
        struct WatchUpdate {
            row_idx: usize,
            new_col: usize,
            watch_slot: usize,
        }
        let mut keep_watching: Vec<usize> = Vec::with_capacity(watching_rows.len());
        let mut watch_updates: Vec<WatchUpdate> = Vec::new();
        let mut satisfied_updates: Vec<usize> = Vec::new();
        let mut propagations: Vec<(Literal, usize)> = Vec::new();
        let mut conflict_row: Option<usize> = None;

        // Immutable borrow phase: examine rows and collect updates
        {
            let rows = self.active_rows();

            for row_idx in watching_rows {
                // Skip satisfied rows
                if self.satisfied_rows[row_idx] {
                    keep_watching.push(row_idx);
                    continue;
                }

                let row = &rows[row_idx];

                // Evaluate the row under current assignments
                match self.evaluate_row(row) {
                    RowState::Conflict => {
                        // Conflict - put back watch and stop processing
                        keep_watching.push(row_idx);
                        conflict_row = Some(row_idx);
                        break;
                    }
                    RowState::Satisfied => {
                        // Row satisfied - mark it and keep watching
                        satisfied_updates.push(row_idx);
                        keep_watching.push(row_idx);
                    }
                    RowState::Unit(unit_col, val) => {
                        // Unit propagation - keep watching and collect
                        // Continue processing to find all propagations
                        keep_watching.push(row_idx);
                        let var = Variable::new(self.col_to_var[unit_col]);
                        let lit = if val {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        };
                        propagations.push((lit, row_idx));
                    }
                    RowState::Unknown => {
                        // 2+ unassigned - try to find a new watch
                        let row_watch = self.row_watches[row_idx];
                        let watch_slot = usize::from(row_watch[0] != Some(assigned_col));

                        // Find a new unassigned column to watch
                        let mut found_new = false;
                        for new_col in 0..self.num_cols {
                            // Must be: in this row, unassigned, and not already watched
                            if row.get(new_col)
                                && self.assignments[new_col].is_none()
                                && row_watch[0] != Some(new_col)
                                && row_watch[1] != Some(new_col)
                            {
                                // Found a new watch
                                watch_updates.push(WatchUpdate {
                                    row_idx,
                                    new_col,
                                    watch_slot,
                                });
                                found_new = true;
                                break;
                            }
                        }

                        if !found_new {
                            // No new watch found - keep watching assigned column
                            keep_watching.push(row_idx);
                        }
                    }
                }
            }
        }

        // Mutable phase: apply all updates
        self.watches[assigned_col] = keep_watching;

        for row_idx in satisfied_updates {
            self.satisfied_rows[row_idx] = true;
        }

        for update in watch_updates {
            // Update row_watches
            self.row_watches[update.row_idx][update.watch_slot] = Some(update.new_col);
            // Add to new column's watch list
            self.watches[update.new_col].push(update.row_idx);
        }

        // Return result in priority order: conflict > propagations > nothing
        if let Some(row_idx) = conflict_row {
            GaussResult::Conflict(row_idx)
        } else if propagations.is_empty() {
            GaussResult::Nothing
        } else if propagations.len() == 1 {
            let (lit, row_idx) = propagations[0];
            GaussResult::Propagate(lit, row_idx)
        } else {
            GaussResult::MultiPropagate(propagations)
        }
    }

    /// Get all current unit propagations with their source row indices.
    pub fn get_all_propagations(&self) -> Vec<(Literal, usize)> {
        let mut props = Vec::new();

        for (row_idx, row) in self.active_rows().iter().enumerate() {
            if let RowState::Unit(col, val) = self.evaluate_row(row) {
                let var = Variable::new(self.col_to_var[col]);
                let lit = if val {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                };
                props.push((lit, row_idx));
            }
        }
        props
    }

    /// Backtrack: unassign a variable.
    pub fn unassign(&mut self, var: VarId) {
        if let Some(&col) = self.var_to_col.get(&var) {
            self.assignments[col] = None;
            self.set_assignment_state(col, None);
        }
    }

    /// Find the first conflicting row, if any.
    ///
    /// Returns the row index of the first row that evaluates to Conflict.
    /// Used to build minimal conflict clauses from the specific row.
    pub fn find_conflict_row(&self) -> Option<usize> {
        self.active_rows()
            .iter()
            .position(|row| matches!(self.evaluate_row(row), RowState::Conflict))
    }

    /// Get propagations for rows watching specific columns.
    ///
    /// This is O(k * avg_watchers) where k = number of columns, much faster than
    /// get_all_propagations() which is O(n * m) for n rows and m columns.
    ///
    /// Returns (propagations, conflict_row) tuple where conflict_row is the index
    /// of the first conflicting row found, if any.
    pub fn get_propagations_for_columns(
        &self,
        columns: &[usize],
    ) -> (Vec<(Literal, usize)>, Option<usize>) {
        let mut props = Vec::new();
        let mut conflict_row = None;
        let mut checked_rows = vec![false; self.rows.len()];
        let rows = self.active_rows();

        for &col in columns {
            if col >= self.watches.len() {
                continue;
            }
            for &row_idx in &self.watches[col] {
                if row_idx >= rows.len() || checked_rows[row_idx] {
                    continue;
                }
                checked_rows[row_idx] = true;

                match self.evaluate_row(&rows[row_idx]) {
                    RowState::Unit(unit_col, val) => {
                        let var = Variable::new(self.col_to_var[unit_col]);
                        let lit = if val {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        };
                        props.push((lit, row_idx));
                    }
                    RowState::Conflict => {
                        if conflict_row.is_none() {
                            conflict_row = Some(row_idx);
                        }
                    }
                    _ => {}
                }
            }
        }
        (props, conflict_row)
    }

    /// Get the column index for a variable, if it exists.
    #[inline]
    pub fn get_column(&self, var: VarId) -> Option<usize> {
        self.var_to_col.get(&var).copied()
    }

    /// Check if a variable is tracked by this solver.
    #[inline]
    pub fn has_variable(&self, var: VarId) -> bool {
        self.var_to_col.contains_key(&var)
    }

    /// Get the current assignment for a column.
    #[inline]
    pub fn assignment_at(&self, col: usize) -> Option<bool> {
        self.assignments.get(col).copied().flatten()
    }

    /// Get the number of XOR constraints.
    pub fn num_constraints(&self) -> usize {
        self.rows.len()
    }

    /// Get the number of variables.
    pub fn num_variables(&self) -> usize {
        self.num_cols
    }

    /// Clear all variable assignments and reset satisfied row tracking.
    pub fn clear_assignments(&mut self) {
        self.assignments.fill(None);
        self.assigned_true_cols.clear_all();
        self.unassigned_cols.fill_ones();
        self.reset_satisfied();
    }

    /// Reset satisfied_rows for backtracking.
    ///
    /// Called when backtracking to clear the satisfied status of rows.
    /// Watches remain valid - they don't depend on assignment state.
    pub fn reset_satisfied(&mut self) {
        self.satisfied_rows.fill(false);
    }

    /// Get the variables in a specific RREF row.
    ///
    /// Used to build minimal reason clauses for propagations. Only variables
    /// that are set in the RREF row are included, which is typically much smaller
    /// than the entire trail.
    ///
    /// Returns a vector of (variable_id, column_index) pairs for variables
    /// in the specified row. Uses efficient bit iteration (O(popcount) not O(num_cols)).
    pub fn get_row_variables(&self, row_idx: usize) -> Vec<(VarId, usize)> {
        let row = &self.active_rows()[row_idx];

        // Use efficient set bits iterator - O(popcount) instead of O(num_cols)
        row.iter_set_bits()
            .map(|col| (self.col_to_var[col], col))
            .collect()
    }

    /// Restore the solver to the initial RREF state.
    ///
    /// This is O(n*m) - copying the saved RREF matrix - instead of
    /// O(n*m*k) for full rebuild + elimination. Used for fast backtracking.
    ///
    /// # Panics
    /// Panics if `eliminate()` was never called (no RREF state saved).
    pub fn restore_rref(&mut self) {
        debug_assert!(
            !self.rref_rows.is_empty() || self.rows.is_empty(),
            "restore_rref called before eliminate()"
        );

        // Restore matrix structure from saved RREF
        // O(n*m) copy instead of O(n*m*k) elimination
        for (row, rref_row) in self.rows.iter_mut().zip(&self.rref_rows) {
            row.bits.copy_from_slice(&rref_row.bits);
        }

        // Restore RHS values
        for (row, &rhs) in self.rows.iter_mut().zip(&self.rref_rhs) {
            row.rhs = rhs;
        }

        // Restore pivot mapping
        self.col_to_pivot_row
            .copy_from_slice(&self.rref_col_to_pivot_row);

        // Clear assignments
        for a in &mut self.assignments {
            *a = None;
        }
        self.assigned_true_cols.clear_all();
        self.unassigned_cols.fill_ones();

        // Reset satisfied rows - watches remain valid
        self.reset_satisfied();
    }
}

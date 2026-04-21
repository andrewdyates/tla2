// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reusable support types for check_sat: theory solver construction and BV clause helpers.

#[cfg(not(kani))]
use hashbrown::HashSet as HbHashSet;
use z4_arrays::ArraySolver;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HbHashSet;
use z4_core::TermStore;
use z4_euf::EufSolver;
use z4_lia::{DiophState, HnfCutKey, LiaSolver, StoredCut};

#[derive(Default)]
pub(super) struct LiaReusableState {
    dioph: DiophState,
    learned_cuts: Vec<StoredCut>,
    seen_hnf_cuts: HbHashSet<HnfCutKey>,
}

impl LiaReusableState {
    pub(super) fn capture(&mut self, solver: &mut LiaSolver<'_>) {
        let (learned_cuts, seen_hnf_cuts) = solver.take_learned_state();
        self.dioph = solver.take_dioph_state();
        self.learned_cuts = learned_cuts;
        self.seen_hnf_cuts = seen_hnf_cuts;
    }

    pub(super) fn restore_into(&mut self, solver: &mut LiaSolver<'_>) -> bool {
        solver.import_dioph_state(std::mem::take(&mut self.dioph));

        let needs_cut_replay = !self.learned_cuts.is_empty();
        if needs_cut_replay || !self.seen_hnf_cuts.is_empty() {
            solver.import_learned_state(
                std::mem::take(&mut self.learned_cuts),
                std::mem::take(&mut self.seen_hnf_cuts),
            );
        }

        needs_cut_replay
    }
}

pub(super) fn build_theory_solvers<'a>(
    terms: &'a TermStore,
    has_array_ops: bool,
    needs_euf: bool,
    start: std::time::Instant,
    timeout: Option<std::time::Duration>,
    lia_state: &mut LiaReusableState,
) -> (
    LiaSolver<'a>,
    Option<ArraySolver<'a>>,
    Option<EufSolver<'a>>,
    bool,
) {
    #[cfg(test)]
    super::record_theory_solver_build_for_tests();

    let mut lia = LiaSolver::new(terms);
    if needs_euf {
        lia.set_combined_theory_mode(true);
    }
    if let Some(timeout) = timeout {
        lia.set_timeout_callback(move || start.elapsed() >= timeout);
    }
    let needs_cut_replay = lia_state.restore_into(&mut lia);

    (
        lia,
        has_array_ops.then(|| ArraySolver::new(terms)),
        needs_euf.then(|| EufSolver::new(terms)),
        needs_cut_replay,
    )
}

pub(super) fn add_offset_bv_clause(
    sat: &mut z4_sat::Solver,
    clause: &z4_core::CnfClause,
    offset: i32,
) {
    let lits: Vec<z4_sat::Literal> = clause
        .literals()
        .iter()
        .map(|&lit| {
            let offset_lit = if lit > 0 { lit + offset } else { lit - offset };
            z4_sat::Literal::from_dimacs(offset_lit)
        })
        .collect();
    sat.add_clause(lits);
}

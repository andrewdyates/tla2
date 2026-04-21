// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction and LIA state preservation for TheoryCombiner.
//!
//! Separated from `combiner.rs` for file-size compliance (#6332 Wave 0).

// Wave 1: TheoryCombiner now used in production dispatch (#6332).

use z4_arrays::ArrayModel;
use z4_core::TermId;
use z4_core::TheoryConflict;
use z4_euf::EufModel;
use z4_lia::{DiophState, HnfCutKey, LiaModel, LiaSolver, StoredCut};
use z4_lra::LraModel;

use super::combiner::TheoryCombiner;
use super::models::{euf_with_int_values, extract_array_model, merge_lia_values, merge_lra_values};

impl TheoryCombiner<'_> {
    // --- Model extraction ---

    pub(crate) fn scope_euf_model_to_roots(&mut self, roots: &[TermId]) {
        self.euf.scope_model_to_roots(roots);
    }

    pub(crate) fn clear_euf_model_scope(&mut self) {
        self.euf.clear_model_scope();
    }

    pub(crate) fn extract_euf_lra_models(&mut self) -> (EufModel, LraModel) {
        let euf_model = euf_with_int_values(&mut self.euf);
        let lra_model = self
            .lra
            .as_mut()
            .expect("extract_euf_lra_models requires LRA")
            .extract_model();
        (euf_model, lra_model)
    }

    pub(crate) fn extract_all_models_auflia(&mut self) -> (EufModel, ArrayModel, Option<LiaModel>) {
        let mut euf_model = euf_with_int_values(&mut self.euf);
        let lia_model = self.lia.as_mut().and_then(|l| l.extract_model());
        merge_lia_values(&mut euf_model, lia_model.as_ref());
        #[cfg(debug_assertions)]
        let lia_value_count = lia_model.as_ref().map_or(0, |m| m.values.len());
        #[cfg(debug_assertions)]
        debug_assert!(
            euf_model.term_values.len() >= lia_value_count,
            "BUG: AUFLIA combiner EUF model has {} values, fewer than LIA model's {} values",
            euf_model.term_values.len(),
            lia_value_count
        );
        let arrays = self
            .arrays
            .as_mut()
            .expect("extract_all_models_auflia requires arrays");
        let array_model = extract_array_model(arrays, &euf_model);
        (euf_model, array_model, lia_model)
    }

    pub(crate) fn extract_all_models_auflra(&mut self) -> (EufModel, ArrayModel, LraModel) {
        let mut euf_model = euf_with_int_values(&mut self.euf);
        let lra = self
            .lra
            .as_mut()
            .expect("extract_all_models_auflra requires LRA");
        let lra_model = lra.extract_model();
        merge_lra_values(&mut euf_model, &lra_model, self.terms);
        #[cfg(debug_assertions)]
        let lra_value_count = lra_model.values.len();
        #[cfg(debug_assertions)]
        debug_assert!(
            euf_model.term_values.len() >= lra_value_count,
            "BUG: AUFLRA combiner EUF model has {} values, fewer than LRA model's {} values",
            euf_model.term_values.len(),
            lra_value_count
        );
        let arrays = self
            .arrays
            .as_mut()
            .expect("extract_all_models_auflra requires arrays");
        let array_model = extract_array_model(arrays, &euf_model);
        (euf_model, array_model, lra_model)
    }

    pub(crate) fn extract_euf_array_models(&mut self) -> (EufModel, ArrayModel) {
        let euf_model = euf_with_int_values(&mut self.euf);
        let arrays = self
            .arrays
            .as_mut()
            .expect("extract_euf_array_models requires arrays");
        let array_model = extract_array_model(arrays, &euf_model);
        (euf_model, array_model)
    }

    // --- LIA state preservation ---

    pub(crate) fn take_learned_state(
        &mut self,
    ) -> Option<(Vec<StoredCut>, hashbrown::HashSet<HnfCutKey>)> {
        self.lia.as_mut().map(LiaSolver::take_learned_state)
    }

    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<StoredCut>,
        seen: hashbrown::HashSet<HnfCutKey>,
    ) {
        if let Some(lia) = &mut self.lia {
            lia.import_learned_state(cuts, seen);
        }
    }

    pub(crate) fn take_dioph_state(&mut self) -> Option<DiophState> {
        self.lia.as_mut().map(LiaSolver::take_dioph_state)
    }

    pub(crate) fn import_dioph_state(&mut self, state: DiophState) {
        if let Some(lia) = &mut self.lia {
            lia.import_dioph_state(state);
        }
    }

    pub(crate) fn replay_learned_cuts(&mut self) {
        if let Some(lia) = &mut self.lia {
            lia.replay_learned_cuts();
        }
        if let Some(lra) = &mut self.lra {
            lra.replay_learned_cuts();
        }
    }

    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    pub(crate) fn collect_all_bound_conflicts(&self, skip_first: bool) -> Vec<TheoryConflict> {
        let mut conflicts = if let Some(lia) = &self.lia {
            lia.collect_all_bound_conflicts(skip_first)
        } else {
            Vec::new()
        };

        let lra_skip_first = skip_first && conflicts.is_empty();
        if let Some(lra) = &self.lra {
            conflicts.extend(lra.collect_all_bound_conflicts(lra_skip_first));
        }

        conflicts
    }
}

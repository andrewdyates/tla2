// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_arrays::{ArrayModel, ArraySolver};
use z4_core::{Sort, TermStore};
use z4_euf::{EufModel, EufSolver};
use z4_lia::LiaModel;
use z4_lra::LraModel;

use crate::executor_format::{format_bigint, format_rational};

/// Extract an EUF model and extend it with Int term values from equivalence classes.
pub(super) fn euf_with_int_values(euf: &mut EufSolver<'_>) -> EufModel {
    let mut euf_model = euf.extract_model();
    let base_count = euf_model.term_values.len();
    euf_model.term_values.extend(euf.extract_int_term_values());
    // Int value extraction should only add new entries, not replace (#4714)
    debug_assert!(
        euf_model.term_values.len() >= base_count,
        "euf_with_int_values: term_values shrank from {} to {}",
        base_count,
        euf_model.term_values.len()
    );
    euf_model
}

/// Merge LIA values into an EUF model for complete Int coverage.
///
/// LIA is authoritative for arithmetic terms. EUF's `extract_int_term_values()`
/// assigns speculative fresh integers to equivalence classes without concrete
/// constants, so disagreement with LIA is expected and LIA's values win.
pub(super) fn merge_lia_values(euf_model: &mut EufModel, lia_model: Option<&LiaModel>) {
    if let Some(lia_model) = lia_model {
        let size_before = euf_model.term_values.len();
        for (&term_id, val) in &lia_model.values {
            euf_model.term_values.insert(term_id, format_bigint(val));
        }
        // Model merge must not shrink the value map (insert only overwrites, never removes)
        debug_assert!(
            euf_model.term_values.len() >= size_before,
            "BUG: merge_lia_values shrank term_values from {} to {}",
            size_before,
            euf_model.term_values.len()
        );
    }
}

/// Merge LRA values into an EUF model for Real-sorted terms.
///
/// LRA is authoritative for Real-sorted terms, same rationale as `merge_lia_values`.
/// Int-sorted terms are skipped: their values come from LIA, and LRA's unconstrained
/// defaults would overwrite correct LIA values with unparseable Real literals (#6291).
pub(super) fn merge_lra_values(euf_model: &mut EufModel, lra_model: &LraModel, terms: &TermStore) {
    let size_before = euf_model.term_values.len();
    for (&term_id, val) in &lra_model.values {
        // Int-sorted terms belong to LIA. Overwriting with LRA's default
        // produces a Real literal ("0.0") that fails Int parsing (#6291).
        if matches!(*terms.sort(term_id), Sort::Int) {
            continue;
        }
        euf_model.term_values.insert(term_id, format_rational(val));
    }
    // Model merge must not shrink the value map (insert only overwrites, never removes)
    debug_assert!(
        euf_model.term_values.len() >= size_before,
        "BUG: merge_lra_values shrank term_values from {} to {}",
        size_before,
        euf_model.term_values.len()
    );
}

/// Build an array model from a merged EUF model term-value map.
///
/// Delegates to `ArraySolver::extract_model` which walks store chains
/// and const-array terms using the merged term-value map from EUF+LIA/LRA.
pub(super) fn extract_array_model(
    arrays: &mut ArraySolver<'_>,
    euf_model: &EufModel,
) -> ArrayModel {
    arrays.extract_model(&euf_model.term_values)
}

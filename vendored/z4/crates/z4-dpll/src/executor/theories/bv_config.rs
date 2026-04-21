// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV solve pipeline configuration.
//!
//! `BvSolveConfig` parameterizes the shared BV solve pipeline in `bv.rs`
//! for each logic variant (QF_BV, QF_ABV, QF_UFBV, QF_AUFBV) and mode
//! (single-shot, incremental push/pop).
//!
//! Split from `bv.rs` for code health (#7006).

/// Configuration for the shared BV solve pipeline.
///
/// Each BV logic variant (QF_BV, QF_ABV, QF_UFBV, QF_AUFBV) uses the same
/// core pipeline with different features enabled. This struct parameterizes
/// those differences so the pipeline is written once.
pub(in crate::executor) struct BvSolveConfig {
    /// Theory label for proof tracking (e.g., "BV", "ARRAY_BV", "UF_BV", "AUF_BV")
    pub theory_tag: &'static str,
    /// Whether to run preprocessing (var_subst, flatten AND/Let) — QF_BV only
    pub preprocess: bool,
    /// Whether to generate array axioms (extensionality, ROW, store congruence)
    pub array_axioms: bool,
    /// Whether to generate EUF congruence axioms for BV-return UFs
    pub uf_congruence: bool,
    /// Whether to generate congruence axioms for non-BV-return UFs (Bool, etc.)
    pub non_bv_congruence: bool,
    /// Whether to generate BV equality congruence axioms (#1708) — QF_BV only
    pub bv_eq_congruence: bool,
    /// Whether to use incremental mode with persistent SAT solver and cached state.
    /// When true, uses IncrementalBvState for Tseitin/BvSolver/SatSolver state
    /// management (push/pop scoping, global definitional clauses). Only QF_BV
    /// currently supports incremental mode.
    pub incremental: bool,
}

impl BvSolveConfig {
    /// Configuration for QF_BV (pure bitvectors).
    pub(in crate::executor) fn qf_bv() -> Self {
        Self {
            theory_tag: "BV",
            preprocess: true,
            array_axioms: false,
            uf_congruence: false,
            non_bv_congruence: false,
            bv_eq_congruence: true,
            incremental: false,
        }
    }

    /// Configuration for QF_BV in incremental mode (push/pop with persistent SAT).
    pub(in crate::executor) fn qf_bv_incremental() -> Self {
        Self {
            theory_tag: "BV",
            // Preprocessing disabled in incremental mode (#1825): variable
            // substitution results can vary based on prior assertions, making
            // original→preprocessed term mappings unstable across check-sat calls.
            preprocess: false,
            array_axioms: false,
            uf_congruence: false,
            non_bv_congruence: false,
            // BV equality congruence axioms enabled for incremental mode (#5441):
            // parity with non-incremental QF_BV path. When (= a b) is asserted
            // and (= a c), (= b c) are bitblasted, adds direct (= a c) ↔ (= b c)
            // equivalences as global clauses.
            bv_eq_congruence: true,
            incremental: true,
        }
    }

    /// Configuration for QF_ABV (arrays + bitvectors).
    ///
    /// Preprocessing is disabled: the variable substitution pass can break
    /// array axiom generation by rewriting select/store terms that the array
    /// theory solver needs to track. This caused 20 regressions when tested.
    pub(in crate::executor) fn qf_abv() -> Self {
        Self {
            theory_tag: "ARRAY_BV",
            preprocess: false,
            array_axioms: true,
            uf_congruence: false,
            non_bv_congruence: false,
            bv_eq_congruence: false,
            incremental: false,
        }
    }

    /// Configuration for QF_ABV in incremental mode.
    pub(in crate::executor) fn qf_abv_incremental() -> Self {
        Self {
            theory_tag: "ARRAY_BV",
            preprocess: false,
            array_axioms: true,
            uf_congruence: false,
            non_bv_congruence: false,
            bv_eq_congruence: false,
            incremental: true,
        }
    }

    /// Configuration for QF_UFBV (uninterpreted functions + bitvectors).
    pub(in crate::executor) fn qf_ufbv() -> Self {
        Self {
            theory_tag: "UF_BV",
            preprocess: false,
            array_axioms: false,
            uf_congruence: true,
            non_bv_congruence: true,
            bv_eq_congruence: false,
            incremental: false,
        }
    }

    /// Configuration for QF_UFBV in incremental mode.
    pub(in crate::executor) fn qf_ufbv_incremental() -> Self {
        Self {
            theory_tag: "UF_BV",
            preprocess: false,
            array_axioms: false,
            uf_congruence: true,
            non_bv_congruence: true,
            bv_eq_congruence: false,
            incremental: true,
        }
    }

    /// Configuration for QF_AUFBV (arrays + UF + bitvectors).
    pub(in crate::executor) fn qf_aufbv() -> Self {
        Self {
            theory_tag: "AUF_BV",
            preprocess: false,
            array_axioms: true,
            uf_congruence: true,
            non_bv_congruence: true,
            bv_eq_congruence: false,
            incremental: false,
        }
    }

    /// Configuration for QF_AUFBV in incremental mode.
    pub(in crate::executor) fn qf_aufbv_incremental() -> Self {
        Self {
            theory_tag: "AUF_BV",
            preprocess: false,
            array_axioms: true,
            uf_congruence: true,
            non_bv_congruence: true,
            bv_eq_congruence: false,
            incremental: true,
        }
    }
}

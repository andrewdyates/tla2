// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core solver: word equation solving via normal forms.
//!
//! Implements the algorithm from Liang et al., "A DPLL(T) Theory Solver for
//! a Theory of Strings and Regular Expressions", CAV 2014.
//!
//! The CVC5 strategy pipeline executes these steps in order:
//! 1. `check_cycles` — detect containment cycles (x = t·x·u implies conflict
//!    if t or u is non-empty).
//! 2. `check_flat_forms` — lightweight pre-check using flattened concat terms.
//! 3. `check_normal_forms_eq_prop` — propagation-only NF equality (buffers splits).
//! 4. `check_extf_eval_effort1` — post-NF extf evaluation pass.
//! 5. `check_normal_forms_eq` — emit one buffered split lemma.
//! 6. `check_normal_forms_deq` — disequality checking via normal forms.
//!
//! Reference: `reference/cvc5/src/theory/strings/core_solver.h`
//! Reference: `reference/cvc5/src/theory/strings/core_solver.cpp`

use crate::arith_entail::ArithEntail;
use crate::infer::{InferenceKind, InferenceManager};
use crate::normal_form::NormalForm;
use crate::regexp::{MatchResult, RegExpSolver};
use crate::skolem::SkolemCache;
use crate::state::SolverState;
#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use std::sync::LazyLock;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, TermData, TermId, TermStore};
use z4_core::{Sort, StringLemma, StringLemmaKind, Symbol, TheoryLit};

mod cycles;
mod explanation;
mod extf_contains;
mod extf_effort1;
mod extf_effort1_helpers;
mod extf_eval;
mod extf_eval_effort1;
mod extf_eval_entailment;
mod extf_pass;
mod extf_pass_int;
mod extf_pass_reductions;
mod flat_forms;
mod nf_deq_process;
mod nf_disequality;
mod nf_equality;
mod nf_equality_simpleq;
mod normal_forms;
#[cfg(test)]
mod tests;

/// Cached debug flag: checked once at process startup instead of 20× per check().
/// Also enabled by `Z4_DEBUG_THEORY=1` umbrella.
static DEBUG_STRING_CORE: LazyLock<bool> = LazyLock::new(|| {
    std::env::var("Z4_DEBUG_STRING_CORE").is_ok() || std::env::var("Z4_DEBUG_THEORY").is_ok()
});

/// Result of a normal form comparison.
///
/// Distinguishes "no conflict, fully resolved" from "no conflict, but
/// bailed out on unresolved variable components".
#[derive(Debug)]
enum NfCheckResult {
    /// A conflict was found and added to the inference manager.
    Conflict,
    /// No conflict; all components were fully resolved.
    Ok,
    /// No conflict, but the comparison bailed out on a variable component
    /// that couldn't be resolved without split lemmas.
    Incomplete,
    /// A split lemma is needed to make progress. The caller must add this
    /// lemma clause to the SAT solver and re-run.
    NeedLemma(StringLemma),
}

#[derive(Copy, Clone, Debug)]
enum IntRelation {
    Lt,
    Le,
    Gt,
    Ge,
}

/// Argument key for extended-function substitution caching.
///
/// During effort-1 evaluation, extf applications are resolved per-argument
/// using the EQC representative or its constant value. This key type
/// identifies each resolved argument for deduplication.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
enum ExtfArgKey {
    Rep(TermId),
    StrConst(String),
    IntConst(BigInt),
}

/// Composite key for deduplicating extended-function evaluations.
///
/// Two extf applications with the same symbol and resolved argument keys
/// will produce identical results, so only the first needs evaluation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
struct ExtfSubstKey {
    symbol: String,
    args: Vec<ExtfArgKey>,
}

/// A recorded `str.contains` fact from the assertion set.
///
/// Used by the contains-overlap checker to detect conflicts between
/// overlapping containment assertions and known string constants.
#[derive(Clone, Copy, Debug)]
struct ContainsFact {
    haystack: TermId,
    needle: TermId,
    lit: TheoryLit,
}

/// Core solver: word equation reasoning via normal forms.
#[derive(Debug, Default)]
pub(crate) struct CoreSolver {
    /// Computed normal forms, keyed by EQC representative.
    normal_forms: HashMap<TermId, NormalForm>,
    /// Flat forms: for each concat term, its flattened component list
    /// (EQC representatives with empties dropped). Computed during cycle check.
    ///
    /// Reference: CVC5 `d_flat_form` in `core_solver.h:589`
    flat_forms: HashMap<TermId, Vec<TermId>>,
    /// Map from canonical NF term vectors to the first EQC with that NF.
    /// Used in `check_normal_forms_eq_prop` to detect identical NFs across
    /// different EQCs and merge them (free propagation).
    ///
    /// Reference: CVC5 `nf_to_eqc` in `core_solver.cpp:562`
    nf_to_eqc: HashMap<Vec<TermId>, TermId>,
    /// Whether the last `check()` was incomplete (unresolved variables).
    ///
    /// Set when NF comparison bails out due to variable components that
    /// cannot be resolved without split lemmas. When true, the solver
    /// cannot soundly claim SAT — should return Unknown instead.
    incomplete: bool,
    /// A pending string split lemma request from `process_simple_neq`.
    ///
    /// Set when NF comparison identifies a split point (Cases 6-9 of CVC5's
    /// processSimpleNEq). The caller retrieves this via `take_pending_lemma()`
    /// and converts it to `TheoryResult::NeedStringLemma`.
    pending_lemma: Option<StringLemma>,
    /// Buffered split lemmas from the propagation-only NF equality pass.
    /// CVC5 stores these in `d_pinfers` and picks the best one in
    /// `checkNormalFormsEq`. This two-phase approach allows extf eval
    /// effort 1 to run between propagation and splitting.
    ///
    /// Reference: CVC5 `d_pinfers` in `core_solver.h:638`
    buffered_lemmas: Vec<StringLemma>,
    /// Terms that have been reduced via DPLL-level reduction lemmas
    /// (e.g., str.substr → word equation + arithmetic). These should NOT
    /// trigger `incomplete` in `check_extf_reductions` because their
    /// semantics are fully captured by the reduction axioms.
    ///
    /// Reference: CVC5 purification in `theory_strings_preprocess.cpp`
    reduced_terms: HashSet<TermId>,
}

impl CoreSolver {
    // Keep recursive string/int resolution within the default Rust test-thread
    // stack budget; deeper chains degrade to `None`/Unknown instead of aborting.
    const MAX_RESOLVE_DEPTH: usize = 16;

    /// Create a new core solver.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Mark a term as having been reduced via DPLL-level reduction lemmas.
    /// Reduced terms are skipped by `check_extf_reductions` (they don't
    /// trigger the `incomplete` flag) because their semantics are captured
    /// by word equations and arithmetic constraints in the SAT encoding.
    pub(crate) fn mark_reduced(&mut self, term: TermId) {
        self.reduced_terms.insert(term);
    }

    /// Request an on-demand reduction lemma for a runtime extf term.
    ///
    /// Symbolic `str.substr` terms are no longer eagerly preregistered when
    /// their bounds are non-constant (#4057). When one of those terms blocks
    /// theory progress, request the same reduction axiom on demand instead of
    /// latching `Unknown` forever.
    fn request_dynamic_extf_lemma(&mut self, terms: &TermStore, term: TermId) -> bool {
        if self.pending_lemma.is_some() {
            return true;
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return false;
        };
        if name == "str.substr" && args.len() == 3 {
            self.pending_lemma = Some(StringLemma {
                kind: StringLemmaKind::SubstrReduction,
                x: term,
                y: term,
                char_offset: 0,
                reason: Vec::new(),
            });
            return true;
        }
        false
    }

    /// Run the core solver pipeline.
    ///
    /// Returns `true` if a conflict was found (caller should stop).
    /// Sets `self.incomplete` if the solver couldn't fully resolve all
    /// string equalities (e.g., unresolved variables without split lemmas).
    ///
    /// `skolems` is used to deduplicate split lemma requests: when multiple
    /// EQC pairs in the same check round would request the same split (e.g.,
    /// EmptySplit on x), only the first request is emitted.
    pub(crate) fn check(
        &mut self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
        skolems: &mut SkolemCache,
    ) -> bool {
        self.pending_lemma = None;

        if *DEBUG_STRING_CORE {
            // Dump term store for a range of IDs to understand numbering.
            for i in 0..terms.len().min(30) {
                let tid = TermId(i as u32);
                let tdata = terms.get(tid);
                if !matches!(
                    tdata,
                    TermData::Const(Constant::Bool(true)) | TermData::Const(Constant::Bool(false))
                ) {
                    eprintln!("[STRING_CORE] term {tid:?} = {tdata:?}");
                }
            }
            // Dump all assertions with their term data.
            for &lit in state.assertions() {
                let (atom, pol) = Self::atom_and_polarity(terms, lit);
                let tdata = terms.get(atom);
                eprintln!("[STRING_CORE] check() assertion: {atom:?} pol={pol} term={tdata:?}");
            }
            // Dump all string-sorted EQC constants for tracing false conflicts.
            let mut eqc_info = Vec::new();
            for &lit in state.assertions() {
                let (atom, _pol) = Self::atom_and_polarity(terms, lit);
                if let TermData::App(_sym, args) = terms.get(atom) {
                    for &arg in args {
                        if *terms.sort(arg) == Sort::String {
                            let s = Self::resolve_string_term(terms, state, arg, 0);
                            if s.is_some() {
                                eqc_info.push(format!("{arg:?}={s:?}"));
                            }
                        }
                    }
                }
            }
            if !eqc_info.is_empty() {
                eprintln!(
                    "[STRING_CORE] check() resolved strings: {}",
                    eqc_info.join(", ")
                );
            }
        }

        // Step 1: Check for containment cycles.
        if self.check_cycles(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_cycles");
            }
            return true;
        }

        // Step 1b: Check flat forms (lightweight pre-NF conflict detection).
        // Flat forms are single-level flattened concat representations — cheaper
        // than full normal forms. Can detect conflicts and infer equalities early.
        // Reference: CVC5 CHECK_FLAT_FORMS in strategy.cpp:138
        self.build_flat_forms(terms, state);
        if self.check_flat_forms(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_flat_forms");
            }
            return true;
        }

        // Step 2: Evaluate extf predicates when arguments resolve to constants.
        if self.check_extf_predicates(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_predicates");
            }
            return true;
        }

        // Step 2b: Evaluate value-returning extf applications and check for
        // conflicts with EQC constants (e.g., str.at("hello",0) in EQC with "e").
        if self.check_extf_reductions(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_reductions");
            }
            return true;
        }
        if self.pending_lemma.is_some() {
            return false;
        }
        if *DEBUG_STRING_CORE && self.incomplete {
            eprintln!("[STRING_CORE] incomplete after check_extf_reductions");
        }

        // Step 2c: Evaluate integer-valued string functions (str.to_int,
        // str.indexof, str.to_code) and check against asserted integer
        // equalities.
        // NOTE: Only check non-length int reductions to avoid false conflicts
        // when EQC state is stale (e.g., x in EQC with "abc" from prior CEGAR
        // iteration but len(x)=1 asserted). str.len is handled by the LIA
        // solver and length axiom infrastructure.
        if self.check_extf_int_reductions(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_int_reductions");
            }
            return true;
        }
        if *DEBUG_STRING_CORE && self.incomplete {
            eprintln!("[STRING_CORE] incomplete after check_extf_int_reductions");
        }

        // Step 2d: Simplify concat terms where all but one child is empty.
        // When str.++(c1, c2, ...) has exactly one non-empty child `c_k`,
        // infer str.++(c1, ..., cn) = c_k. This breaks mutual NF dependency
        // cycles that arise after I_CYCLE infers extras="" (#3850).
        if self.simplify_singleton_concats(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from simplify_singleton_concats");
            }
            return true;
        }

        // Step 3: Compute normal forms for all EQCs.
        self.compute_normal_forms(terms, state);

        // Step 4: NF equality — propagation only (CVC5 CHECK_NORMAL_FORMS_EQ_PROP).
        // Detects conflicts, infers internal equalities from identical NFs
        // across EQCs, and buffers split lemmas for later emission.
        // Reference: CVC5 strategy.cpp:142
        match self.check_normal_forms_eq_prop(terms, state, infer, skolems) {
            NfCheckResult::Conflict => {
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] conflict from check_normal_forms_eq_prop");
                }
                return true;
            }
            NfCheckResult::Incomplete => {
                self.incomplete = true;
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] incomplete from check_normal_forms_eq_prop");
                }
            }
            NfCheckResult::Ok => {}
            NfCheckResult::NeedLemma(_) => unreachable!("prop phase buffers lemmas"),
        }

        // Step 4b: Re-evaluate extf terms using NF-derived substitutions.
        // Running this BEFORE emitting split lemmas allows extf reduction
        // to resolve things cheaply, avoiding unnecessary splits.
        // Reference: CVC5 strategy.cpp:144
        if self.check_extf_eval_effort1(terms, state, infer) {
            if *DEBUG_STRING_CORE {
                eprintln!("[STRING_CORE] conflict from check_extf_eval_effort1");
            }
            return true;
        }

        // Step 4c: NF equality — emit one buffered split lemma (CVC5 CHECK_NORMAL_FORMS_EQ).
        // If the prop phase buffered a split candidate and extf eval didn't
        // resolve it, emit the split now.
        // Reference: CVC5 strategy.cpp:143
        match self.check_normal_forms_eq() {
            NfCheckResult::NeedLemma(lemma) => {
                self.pending_lemma = Some(lemma);
                return false;
            }
            NfCheckResult::Ok => {}
            NfCheckResult::Conflict | NfCheckResult::Incomplete => {}
        }

        // Step 5: Check normal form disequalities (#4070).
        match self.check_normal_forms_deq(terms, state, infer, skolems) {
            NfCheckResult::Conflict => {
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] conflict from check_normal_forms_deq");
                }
                return true;
            }
            NfCheckResult::NeedLemma(lemma) => {
                self.pending_lemma = Some(lemma);
                return false;
            }
            NfCheckResult::Incomplete => {
                self.incomplete = true;
                if *DEBUG_STRING_CORE {
                    eprintln!("[STRING_CORE] incomplete from check_normal_forms_deq");
                }
            }
            NfCheckResult::Ok => {}
        }

        false
    }

    /// Get the normal form for an EQC representative.
    #[cfg(test)]
    pub(crate) fn get_normal_form(&self, rep: &TermId) -> Option<&NormalForm> {
        self.normal_forms.get(rep)
    }

    /// Whether the last check was incomplete due to unresolved variables.
    pub(crate) fn is_incomplete(&self) -> bool {
        self.incomplete
    }

    /// Take a pending string split lemma request, if any.
    pub(crate) fn take_pending_lemma(&mut self) -> Option<StringLemma> {
        self.pending_lemma.take()
    }

    /// Clear computed state for a new check round.
    pub(crate) fn clear(&mut self) {
        self.normal_forms.clear();
        self.flat_forms.clear();
        self.nf_to_eqc.clear();
        self.incomplete = false;
        self.pending_lemma = None;
        self.buffered_lemmas.clear();
    }
}

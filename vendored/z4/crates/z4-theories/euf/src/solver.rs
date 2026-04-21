// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF solver core implementation.
//!
//! Contains `EufSolver` struct definition, constructor, and utility methods.
//! Incremental E-graph operations are in `egraph.rs`.

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use std::collections::VecDeque;
use std::sync::OnceLock;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, TermData, TermId, TermStore};
use z4_core::{Sort, TheoryLit};

/// #6359: Cached debug flags for EUF solver.
struct EufDebugFlags {
    debug_euf: bool,
    debug_nelson_oppen: bool,
}

static EUF_DEBUG_FLAGS: OnceLock<EufDebugFlags> = OnceLock::new();

fn euf_debug_flags() -> &'static EufDebugFlags {
    EUF_DEBUG_FLAGS.get_or_init(|| EufDebugFlags {
        debug_euf: std::env::var("Z4_DEBUG_EUF").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        debug_nelson_oppen: std::env::var("Z4_DEBUG_EUF_NELSON_OPPEN").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
    })
}

use crate::types::{
    CongruenceTable, ENode, EqualityReason, FuncAppMeta, MergeReason, UndoRecord, UnionFind,
};

/// EUF theory solver
pub struct EufSolver<'a> {
    pub(crate) terms: &'a TermStore,
    pub(crate) uf: UnionFind,
    pub(crate) assigns: HashMap<TermId, bool>,
    pub(crate) trail: Vec<(TermId, Option<bool>)>,
    pub(crate) scopes: Vec<usize>,
    pub(crate) dirty: bool,
    /// Equality graph: maps (min(a,b), max(a,b)) -> reason why a = b
    pub(crate) equality_edges: HashMap<(u32, u32), EqualityReason>,
    /// Pre-computed list of function application terms with their argument ids
    /// This avoids iterating all terms and cloning during congruence closure
    pub(crate) func_apps: Vec<FuncAppMeta>,
    /// Index from term_id -> index in func_apps for O(1) lookup
    pub(crate) func_app_index: HashMap<u32, usize>,
    /// Whether func_apps has been initialized
    pub(crate) func_apps_init: bool,
    /// Direct conflict detected when assigning term to both true and false
    /// Stores (term, positive_assignment) - the conflict is between term=true and term=false
    pub(crate) pending_conflict: Option<TermId>,

    // ========================================================================
    // Incremental E-graph structures (Phase 1 infrastructure)
    // ========================================================================
    /// E-nodes indexed by term ID - tracks class membership and parent pointers
    pub(crate) enodes: Vec<ENode>,
    /// Whether enodes have been initialized
    pub(crate) enodes_init: bool,
    /// Persistent congruence table
    pub(crate) cong_table: CongruenceTable,
    /// Worklist of pending merges to process
    pub(crate) to_merge: VecDeque<MergeReason>,
    /// Undo trail for push/pop support
    pub(crate) undo_trail: Vec<UndoRecord>,
    /// Scope marks for undo trail
    pub(crate) undo_scopes: Vec<usize>,
    // ========================================================================
    // Nelson-Oppen shared equality state
    // ========================================================================
    /// Shared equalities from other theories (e.g., LIA discovering x = y).
    /// Format: (min(lhs,rhs), max(lhs,rhs)) -> reason_literals
    pub(crate) shared_equality_reasons: HashMap<(u32, u32), Vec<TheoryLit>>,
    /// Equality assertions already propagated to other theories.
    /// Tracks the equality term ID (= lhs rhs) to avoid duplicate propagation.
    pub(crate) propagated_eqs: HashSet<TermId>,
    /// Congruence-derived equalities already propagated to other theories.
    /// Tracks (min(lhs, rhs), max(lhs, rhs)) pairs for canonical ordering.
    /// Added for #319 - congruence-derived equalities must also be propagated.
    pub(crate) propagated_eq_pairs: HashSet<(TermId, TermId)>,
    /// Pending equalities to propagate to other theories (EUF→LIA direction).
    /// Populated by rebuild_closure(), drained by propagate_equalities().
    /// Format: (lhs, rhs, reason_literals)
    pub(crate) pending_propagations: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    // ========================================================================
    // Function application value tracking (#385)
    // ========================================================================
    /// Tracks constant values for function applications returning Int/Real/BV.
    /// When `(= (f x) 100)` is asserted as true, stores (func_app_term_id, const_term_id).
    /// Used by extract_model() to provide actual values in EufModel.func_app_const_terms.
    pub(crate) func_app_values: HashMap<TermId, TermId>,
    /// Optional extraction scope for model building.
    ///
    /// In incremental mode, the append-only TermStore retains terms from popped
    /// scopes. Model extraction must ignore terms that are no longer reachable
    /// from the live assertion roots, or dead predicate applications can shadow
    /// live interpretations in the function table (#6813).
    pub(crate) model_term_scope: Option<HashSet<TermId>>,
    // ========================================================================
    // Pre-indexed equality terms (#2673)
    // ========================================================================
    /// Pre-computed list of equality terms: (eq_term_id, lhs, rhs).
    /// Avoids scanning all terms in propagate(). Initialized lazily like func_apps.
    pub(crate) eq_terms: Vec<(TermId, TermId, TermId)>,
    /// Whether eq_terms has been initialized
    pub(crate) eq_terms_init: bool,
    // ========================================================================
    // Pre-indexed ITE terms (#5575)
    // ========================================================================
    /// Pre-computed list of ITE term indices (non-Bool sort only).
    /// Avoids scanning all terms in rebuild_closure/incremental_rebuild.
    pub(crate) ite_terms: Vec<u32>,
    /// Whether ite_terms has been initialized
    pub(crate) ite_terms_init: bool,
    // ========================================================================
    // Reusable scratch buffers (#5575)
    // ========================================================================
    /// Scratch buffer for check() disequality collection (Stage 1)
    pub(crate) scratch_diseqs: Vec<(TermId, TermId, TermId)>,
    /// Scratch buffer for check() distinct constraints (Stage 2)
    pub(crate) scratch_distincts: Vec<(TermId, Vec<TermId>)>,
    /// Scratch buffer for check() constant conflict detection (Stage 3)
    pub(crate) scratch_rep_to_const: HashMap<u32, (TermId, Constant)>,
    /// Scratch buffer for check() Boolean congruence (Stage 4)
    pub(crate) scratch_bool_terms: Vec<(TermId, bool)>,
    /// Scratch buffer for check() Boolean rep tracking (Stage 4)
    pub(crate) scratch_rep_value: HashMap<u32, (TermId, bool)>,
    /// Scratch buffer for propagate() positive equality candidates
    pub(crate) scratch_potential_props: Vec<(TermId, TermId, TermId)>,
    /// Scratch buffer for propagate() disequality index
    pub(crate) scratch_diseq_index: HashMap<(u32, u32), (TermId, TermId, TermId)>,
    /// Scratch buffer for propagate() negative propagation candidates
    pub(crate) scratch_neg_props: Vec<(TermId, TermId, TermId, TermId, TermId, TermId)>,
    /// Scratch buffer for rebuild_closure() equalities to propagate
    pub(crate) scratch_equalities: Vec<(TermId, TermId, TermId)>,
    /// Scratch buffer for rebuild_closure() shared equality keys
    pub(crate) scratch_shared_eq_keys: Vec<(u32, u32)>,
    // ========================================================================
    // Cached env vars (#2673)
    // ========================================================================
    /// Cached Z4_DEBUG_EUF flag (avoids syscall per hot-path call)
    pub(crate) debug_euf: bool,
    /// Cached Z4_DEBUG_EUF_NELSON_OPPEN flag
    pub(crate) debug_nelson_oppen: bool,
    // Per-theory runtime statistics (#4706)
    pub(crate) check_count: u64,
    pub(crate) conflict_count: u64,
    pub(crate) propagation_count: u64,
}

impl<'a> EufSolver<'a> {
    #[inline]
    pub(crate) fn debug_assert_enode_index(&self, term: u32, context: &str) {
        debug_assert!(
            (term as usize) < self.enodes.len(),
            "BUG: {context}: out-of-bounds term id {term} (enodes len={})",
            self.enodes.len()
        );
    }

    #[inline]
    pub(crate) fn debug_assert_enode_root_fixed_point(&self, rep: u32, context: &str) {
        debug_assert!(
            (rep as usize) < self.enodes.len() && self.enodes[rep as usize].root == rep,
            "BUG: {context}: representative {rep} must be a fixed-point root (enodes len={})",
            self.enodes.len()
        );
    }

    #[inline]
    pub(crate) fn debug_assert_solver_term_index(&self, term: TermId, context: &str) {
        debug_assert!(
            (term.0 as usize) < self.terms.len(),
            "BUG: {context}: term {} out of range (term store len={})",
            term.0,
            self.terms.len()
        );
    }

    #[inline]
    pub(crate) fn debug_assert_explain_lca(&self, lca: u32, root: u32) {
        debug_assert!(
            (lca as usize) < self.enodes.len(),
            "BUG: explain LCA out of bounds: {lca} (enodes len={})",
            self.enodes.len()
        );
        debug_assert_eq!(
            self.find_proof_root(lca),
            root,
            "BUG: explain LCA must stay in the same proof tree"
        );
    }

    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_enode_class_integrity(&self, root: u32, context: &str) {
        let root_in_bounds = (root as usize) < self.enodes.len();
        debug_assert!(
            root_in_bounds,
            "BUG: {context}: root {root} out of bounds (enodes len={})",
            self.enodes.len()
        );
        if !root_in_bounds {
            return;
        }
        self.debug_assert_enode_root_fixed_point(root, context);

        let start = root;
        let mut curr = root;
        let mut count = 0u32;
        let max_nodes = self.enodes.len() as u32;

        loop {
            let curr_in_bounds = (curr as usize) < self.enodes.len();
            debug_assert!(
                curr_in_bounds,
                "BUG: {context}: class walk hit out-of-bounds node {curr} (enodes len={})",
                self.enodes.len()
            );
            if !curr_in_bounds {
                return;
            }
            debug_assert_eq!(
                self.enode_find_const(curr),
                root,
                "BUG: {context}: node {curr} in class walk does not map to root {root}"
            );
            count += 1;
            debug_assert!(
                count <= max_nodes,
                "BUG: {context}: class walk exceeded enode count while traversing root {root}"
            );
            let next = self.enodes[curr as usize].next;
            let next_in_bounds = (next as usize) < self.enodes.len();
            debug_assert!(
                next_in_bounds,
                "BUG: {context}: class walk next pointer out of bounds: {next} (enodes len={})",
                self.enodes.len()
            );
            if !next_in_bounds {
                return;
            }
            curr = next;
            if curr == start {
                break;
            }
        }

        debug_assert_eq!(
            count, self.enodes[root as usize].class_size,
            "BUG: {context}: class_size mismatch for root {root}"
        );
    }

    /// Create a new EUF solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        EufSolver {
            terms,
            uf: UnionFind::new(terms.len()),
            assigns: HashMap::new(),
            trail: Vec::new(),
            scopes: Vec::new(),
            dirty: true,
            equality_edges: HashMap::new(),
            func_apps: Vec::new(),
            func_app_index: HashMap::new(),
            func_apps_init: false,
            pending_conflict: None,
            // Incremental E-graph (Phase 1)
            enodes: Vec::new(),
            enodes_init: false,
            cong_table: CongruenceTable::new(),
            to_merge: VecDeque::new(),
            undo_trail: Vec::new(),
            undo_scopes: Vec::new(),
            // Nelson-Oppen
            shared_equality_reasons: HashMap::new(),
            propagated_eqs: HashSet::new(),
            propagated_eq_pairs: HashSet::new(),
            pending_propagations: Vec::new(),
            // Function application value tracking (#385)
            func_app_values: HashMap::new(),
            model_term_scope: None,
            // Pre-indexed equality terms (#2673)
            eq_terms: Vec::new(),
            eq_terms_init: false,
            // Pre-indexed ITE terms (#5575)
            ite_terms: Vec::new(),
            ite_terms_init: false,
            // Reusable scratch buffers (#5575)
            scratch_diseqs: Vec::new(),
            scratch_distincts: Vec::new(),
            scratch_rep_to_const: HashMap::new(),
            scratch_bool_terms: Vec::new(),
            scratch_rep_value: HashMap::new(),
            scratch_potential_props: Vec::new(),
            scratch_diseq_index: HashMap::new(),
            scratch_neg_props: Vec::new(),
            scratch_equalities: Vec::new(),
            scratch_shared_eq_keys: Vec::new(),
            // #6359: Use process-level cached env vars (OnceLock) to avoid
            // syscalls on every DPLL(T) iteration.
            debug_euf: euf_debug_flags().debug_euf,
            // Incremental EUF (#5575): worklist-based approach processes only
            // new merges per check(). Enabled by default (#6546) — the legacy
            // full-rebuild path is O(assigns) per check() which dominates
            // storeinv benchmarks (11x slower on size 9). Set Z4_LEGACY_EUF=1
            // to force the old rebuild_closure path. Read directly from env
            debug_nelson_oppen: euf_debug_flags().debug_nelson_oppen,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        }
    }

    /// No-op: EUF has no learned cuts to replay.
    /// Required by `solve_incremental_split_loop_pipeline!` macro.
    pub fn replay_learned_cuts(&mut self) {}

    /// Restrict the next model extraction to terms reachable from `roots`.
    pub fn scope_model_to_roots(&mut self, roots: &[TermId]) {
        let mut reachable = HashSet::with_capacity(roots.len().saturating_mul(4));
        let mut stack = roots.to_vec();
        while let Some(term) = stack.pop() {
            if !reachable.insert(term) {
                continue;
            }
            for child in self.terms.children(term) {
                stack.push(child);
            }
        }
        self.model_term_scope = Some(reachable);
    }

    /// Clear any temporary model extraction scope.
    pub fn clear_model_scope(&mut self) {
        self.model_term_scope = None;
    }

    pub(crate) fn scoped_model_terms(&self) -> Vec<TermId> {
        match &self.model_term_scope {
            Some(scope) => {
                let mut terms: Vec<TermId> = scope.iter().copied().collect();
                terms.sort_unstable();
                terms
            }
            None => self.terms.term_ids().collect(),
        }
    }

    /// Initialize the func_apps cache if not already done
    pub(crate) fn init_func_apps(&mut self) {
        if self.func_apps_init {
            return;
        }

        self.func_apps.clear();
        self.func_app_index.clear();
        for term_id in self.terms.term_ids() {
            if let TermData::App(sym, args) = self.terms.get(term_id) {
                if !Self::is_builtin_symbol(sym) && !args.is_empty() {
                    // Pre-compute hash of (symbol, sort)
                    use std::hash::{Hash, Hasher};
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    sym.hash(&mut hasher);
                    self.terms.sort(term_id).hash(&mut hasher);
                    let func_hash = hasher.finish();

                    // Store index for O(1) lookup
                    self.func_app_index.insert(term_id.0, self.func_apps.len());
                    self.func_apps.push(FuncAppMeta {
                        term_id: term_id.0,
                        func_hash,
                        args: args.iter().map(|t| t.0).collect(),
                    });
                }
            }
        }
        self.func_apps_init = true;
    }

    /// Initialize the eq_terms cache: pre-index all equality terms in the TermStore.
    /// Called lazily before first propagate(). Since terms is an immutable borrow,
    /// the index is stable for the solver's lifetime. (#2673)
    pub(crate) fn init_eq_terms(&mut self) {
        if self.eq_terms_init {
            return;
        }
        self.eq_terms.clear();
        for term_id in self.terms.term_ids() {
            if let Some((lhs, rhs)) = self.decode_eq(term_id) {
                self.eq_terms.push((term_id, lhs, rhs));
            }
        }
        self.eq_terms_init = true;
    }

    /// Pre-compute ITE term indices (non-Bool only) for fast iteration (#5575).
    /// Avoids scanning all terms in rebuild_closure/incremental_rebuild when
    /// there are no ITE terms (common in QF_UF, QF_EUF).
    pub(crate) fn init_ite_terms(&mut self) {
        if self.ite_terms_init {
            return;
        }
        self.ite_terms.clear();
        for term_id in self.terms.term_ids() {
            if matches!(self.terms.get(term_id), TermData::Ite(..))
                && !matches!(self.terms.sort(term_id), Sort::Bool)
            {
                self.ite_terms.push(term_id.0);
            }
        }
        self.ite_terms_init = true;
    }

    pub(crate) fn queue_pending_propagation(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: Vec<TheoryLit>,
        context: &'static str,
    ) {
        if lhs == rhs {
            if self.debug_euf || self.debug_nelson_oppen {
                safe_eprintln!(
                    "[EUF] Skipping trivial N-O propagation ({context}): {} = {}",
                    lhs.0,
                    rhs.0
                );
            }
            return;
        }

        self.pending_propagations.push((lhs, rhs, reason));
    }

    /// Current number of terms managed by the solver.
    #[must_use]
    pub fn num_terms(&self) -> usize {
        self.uf.parent.len()
    }
}

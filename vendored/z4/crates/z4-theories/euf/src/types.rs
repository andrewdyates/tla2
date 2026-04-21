// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Data types for the EUF theory solver.
//!
//! Contains union-find, E-node, congruence table, and model types.

#[cfg(not(kani))]
use hashbrown::HashMap;
use num_bigint::BigInt;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermId;

/// Model for uninterpreted sorts - maps sort names to element enumerations
pub type SortModel = HashMap<String, Vec<String>>;

/// Function table entry: maps argument values to result value
pub type FunctionTable = Vec<(Vec<String>, String)>;

/// Model for uninterpreted functions
#[derive(Debug, Clone, Default)]
pub struct EufModel {
    /// Element representatives for each uninterpreted sort
    /// Maps sort name -> list of distinct element names
    pub sort_elements: SortModel,
    /// Maps term IDs to their model element name
    pub term_values: HashMap<TermId, String>,
    /// Function interpretations as finite tables
    /// Maps function name -> list of (arg_values, result_value) entries
    pub function_tables: HashMap<String, FunctionTable>,
    /// Function application values for Int/Real/BV-returning UF applications.
    /// Maps function application term ID -> constant term ID that equals it.
    /// This enables get-value to return the actual value for `(f x)` when
    /// we have `(= (f x) 100)` in assertions.
    pub func_app_const_terms: HashMap<TermId, TermId>,
    /// Distinct integer values for Int-sorted terms managed by EUF.
    /// Each equivalence class gets a unique integer so that disequalities
    /// are respected when no LIA/LRA model is available (#3172).
    pub int_values: HashMap<TermId, BigInt>,
}

// ============================================================================
// Incremental E-Graph Data Structures
// ============================================================================

/// E-node: A term in the E-graph with equivalence class tracking and parent pointers.
///
/// Each ENode maintains:
/// - `root`: The representative of its equivalence class
/// - `next`: Circular linked list of class members (for iteration)
/// - `parents`: Function applications that use this term as an argument
/// - `class_size`: Number of members in the class (only valid at root)
///
/// Reference: Z3's `euf_enode.h`
#[derive(Clone, Debug)]
pub(crate) struct ENode {
    /// Representative of the equivalence class
    pub(crate) root: u32,
    /// Next node in circular list of equivalence class members
    pub(crate) next: u32,
    /// Size of equivalence class (only meaningful at root)
    pub(crate) class_size: u32,
    /// Parent function applications using this term as an argument.
    /// When we merge two classes, we must update the congruence table
    /// for all parent applications.
    pub(crate) parents: Vec<u32>,
    /// Proof-forest parent: the node this was merged into. None = tree root.
    /// Reference: Z3's euf_enode.h m_target
    pub(crate) proof_target: Option<u32>,
    /// Reason for the proof edge to proof_target.
    /// Reference: Z3's euf_enode.h m_justification
    pub(crate) proof_justification: Option<EqualityReason>,
}

impl ENode {
    /// Create a new ENode for a term
    pub(crate) fn new(id: u32) -> Self {
        Self {
            root: id,
            next: id, // Self-loop for singleton class
            class_size: 1,
            parents: Vec::new(),
            proof_target: None,
            proof_justification: None,
        }
    }
}

/// Compact congruence signature — zero heap allocation (#5575).
///
/// Uses a u128 hash of (func_hash, arg_representatives) as the table key.
/// This avoids Vec<u32> allocation per signature, which was the main
/// allocation hotspot in the incremental E-graph merge path.
///
/// Collision safety: `insert()` returns matches purely by signature.
/// Callers MUST verify actual congruence (same func_hash + pairwise-equal
/// arg representatives) before trusting a match. See #6153.
pub(crate) type Signature = u128;

/// Compute a compact signature hash from function hash and argument representatives.
/// No heap allocation — uses bit mixing to combine func_hash with arg reps.
#[inline]
fn compute_signature(func_hash: u64, args: &[u32], enodes: &[ENode]) -> Signature {
    let mut h = u128::from(func_hash);
    // Mix in argument count to differentiate f(a) from f(a, b)
    h = h.wrapping_mul(0x9E3779B97F4A7C15_u128) ^ (args.len() as u128);
    for &arg in args {
        // Follow root pointers to get representative
        let mut curr = arg;
        while enodes[curr as usize].root != curr {
            curr = enodes[curr as usize].root;
        }
        // Mix representative into hash
        h = h.wrapping_mul(0x517CC1B727220A95_u128) ^ u128::from(curr);
    }
    h
}

/// Persistent congruence table for incremental closure.
///
/// Maps compact signature hashes to their canonical representative term.
/// Uses u128 signatures to avoid Vec allocation in the hot merge path.
///
/// Reference: Z3's `euf_etable.h`
#[derive(Clone, Debug, Default)]
pub(crate) struct CongruenceTable {
    /// Maps signature hash -> canonical term ID
    table: HashMap<Signature, u32>,
}

impl CongruenceTable {
    /// Create a new empty congruence table
    pub(crate) fn new() -> Self {
        Self {
            table: HashMap::new(),
        }
    }

    /// Build a compact signature for a function application.
    /// Zero heap allocation — uses u128 hash (#5575).
    pub(crate) fn make_signature(func_hash: u64, args: &[u32], enodes: &[ENode]) -> Signature {
        compute_signature(func_hash, args, enodes)
    }

    /// Insert a term into the table.
    ///
    /// Returns `Some(other)` if a congruent term already exists, `None` otherwise.
    pub(crate) fn insert(&mut self, term: u32, sig: Signature) -> Option<u32> {
        if let Some(&existing) = self.table.get(&sig) {
            if existing != term {
                return Some(existing);
            }
            // Already in table with same term, no action needed
            None
        } else {
            self.table.insert(sig, term);
            None
        }
    }

    /// Remove a term from the table by its signature.
    pub(crate) fn remove(&mut self, sig: &Signature) {
        self.table.remove(sig);
    }

    /// Clear all entries
    pub(crate) fn clear(&mut self) {
        self.table.clear();
    }

    /// Number of entries in the table (for testing)
    #[cfg(test)]
    pub(crate) fn table_len(&self) -> usize {
        self.table.len()
    }

    /// Whether the table is empty (for testing)
    #[cfg(test)]
    pub(crate) fn table_is_empty(&self) -> bool {
        self.table.is_empty()
    }
}

/// Undo record for incremental push/pop support.
///
/// When we push a scope, we save the undo stack length.
/// When we pop, we replay undo records in reverse order.
#[derive(Clone, Debug)]
pub(crate) enum UndoRecord {
    /// Restore a node's root pointer
    SetRoot {
        node: u32,
        old_root: u32,
        old_next: u32,
    },
    /// Restore root's class size
    SetClassSize { node: u32, old_size: u32 },
    /// Remove a parent from a node's parent list
    RemoveParent { node: u32 },
    /// Remove an equality edge added during incremental_merge (#3734)
    RemoveEqualityEdge(u32, u32),
    /// Undo a proof-forest merge: clear node's proof target and reverse the
    /// old root's justification chain to restore pre-merge proof tree.
    /// Port of Z3's unmerge_justification (euf_enode.cpp).
    UnmergeProofForest { node: u32, old_root: u32 },
    /// Remove a shared equality reason added during assert_shared_equality (#4840).
    /// Enables scope-aware cleanup instead of blanket clear, preventing
    /// proof-forest explain() from finding dangling Shared reason references.
    RemoveSharedEqualityReason(u32, u32),
}

// ============================================================================
// Original Union-Find (kept for compatibility during transition)
// ============================================================================

/// Union-Find structure for equivalence classes
pub(crate) struct UnionFind {
    pub(crate) parent: Vec<u32>,
    pub(crate) rank: Vec<u32>,
}

impl UnionFind {
    /// Create a new union-find with n elements
    #[must_use]
    #[allow(clippy::cast_possible_truncation)] // n is bounded by term count which fits in u32
    pub(crate) fn new(n: usize) -> Self {
        Self {
            parent: (0..n as u32).collect(),
            rank: vec![0; n],
        }
    }

    pub(crate) fn reset(&mut self) {
        for (idx, p) in self.parent.iter_mut().enumerate() {
            *p = idx as u32;
        }
        self.rank.fill(0);
    }

    pub(crate) fn ensure_size(&mut self, n: usize) {
        if n <= self.parent.len() {
            return;
        }
        let start = self.parent.len() as u32;
        self.parent
            .extend(start..start + (n - self.parent.len()) as u32);
        self.rank.resize(n, 0);
    }

    /// Find the representative of an element (with path compression)
    pub(crate) fn find(&mut self, x: u32) -> u32 {
        if self.parent[x as usize] != x {
            self.parent[x as usize] = self.find(self.parent[x as usize]);
        }
        self.parent[x as usize]
    }

    /// Union two elements
    #[cfg_attr(not(kani), allow(dead_code))]
    pub(crate) fn union(&mut self, x: u32, y: u32) {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx != ry {
            match self.rank[rx as usize].cmp(&self.rank[ry as usize]) {
                std::cmp::Ordering::Less => {
                    self.parent[rx as usize] = ry;
                }
                std::cmp::Ordering::Greater => {
                    self.parent[ry as usize] = rx;
                }
                std::cmp::Ordering::Equal => {
                    self.parent[ry as usize] = rx;
                    self.rank[rx as usize] += 1;
                }
            }
        }
    }
}

/// Reason for an edge in the equality graph
#[derive(Clone, Debug)]
pub(crate) enum EqualityReason {
    /// Direct equality assertion: the TermId of the (= a b) term
    Direct(TermId),
    /// Congruence: f(a1,...,an) = f(b1,...,bn) because ai = bi for all i
    Congruence {
        /// The two congruent terms (for future proof generation)
        _term1: TermId,
        _term2: TermId,
        /// Pairs of arguments that must be equal
        arg_pairs: Vec<(TermId, TermId)>,
    },
    /// Shared equality from Nelson-Oppen theory combination.
    /// The actual reason literals are stored in `EufSolver::shared_equality_reasons`.
    Shared,
    /// Bool-value merge: two terms share the same Boolean truth value.
    /// The edge between `term` and its canonical representative exists because
    /// both were assigned the stored `value`. (#4610)
    BoolValue {
        /// The term merged with the canonical representative
        term: TermId,
        /// The truth value assigned to both
        value: bool,
    },
    /// ITE axiom: `ite(c, t, e) = t` when `c = true`, or `ite(c, t, e) = e` when `c = false`.
    /// The condition term is stored so explain() can produce the reason. (#5081)
    Ite {
        /// The condition term that was assigned
        condition: TermId,
        /// The truth value of the condition
        value: bool,
    },
}

/// Cached metadata for a function application term
pub(crate) struct FuncAppMeta {
    pub(crate) term_id: u32,
    /// Pre-computed hash of (symbol, result_sort) for fast signature lookup
    pub(crate) func_hash: u64,
    /// Argument term ids (not representatives - those change)
    pub(crate) args: Vec<u32>,
}

/// Reason why two terms should be merged (for worklist processing)
#[derive(Clone, Debug)]
pub(crate) struct MergeReason {
    /// First term
    pub(crate) a: u32,
    /// Second term
    pub(crate) b: u32,
    /// Why they are equal
    pub(crate) reason: EqualityReason,
}

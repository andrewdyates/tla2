// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term representation for Z4
//!
//! Terms are represented as a hash-consed DAG for efficient sharing.
//! The `TermStore` manages term creation and ensures structural sharing
//! through hash-consing.

use crate::kani_compat::KaniHashMap;
use crate::sort::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicUsize, Ordering};

mod arith_div_cmp;
mod arithmetic;
mod arithmetic_sub_mul;
mod array;
mod bitvector;
mod boolean;
mod boolean_eq;
mod builders;
mod cardinality;
mod expand_select_store;
mod ite_lifting;
mod preprocess;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

/// Global counter tracking approximate bytes allocated across ALL TermStore instances.
///
/// Each portfolio engine has its own TermStore. This atomic provides cross-engine
/// visibility into aggregate memory consumption, enabling the portfolio coordinator
/// or engine cancellation checks to detect OOM conditions before they crash the process.
///
/// The count is approximate: it tracks `size_of::<TermEntry>()` per interned term
/// but does not account for heap allocations within `TermData` variants (e.g.,
/// `Vec<TermId>` children in `App`, `String` in constants). The actual memory
/// usage is higher, so the limit should be set conservatively.
static GLOBAL_TERM_BYTES: AtomicUsize = AtomicUsize::new(0);

/// Default memory limit for aggregate TermStore allocation: 4 GB.
///
/// This prevents the portfolio's 8 concurrent engines from collectively
/// exhausting system memory. Each engine builds independent expression trees,
/// so total allocation grows linearly with engine count.
const DEFAULT_TERM_MEMORY_LIMIT: usize = 4 * 1024 * 1024 * 1024;

/// A term identifier (index into the term store)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[must_use = "TermId must be used (discarding it usually indicates a bug)"]
pub struct TermId(pub u32);

impl TermId {
    /// Sentinel value used by the LRA simplex solver for bounds that have no
    /// SAT-level atom reason (e.g., Gomory/HNF cuts, model-seed probing).
    /// Must never collide with a real interned term ID.
    pub const SENTINEL: Self = Self(u32::MAX);

    /// Create a new TermId
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Returns true if this is the sentinel (no real atom reason).
    pub fn is_sentinel(self) -> bool {
        self.0 == u32::MAX
    }

    /// Get the raw index
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for TermId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// Internal term representation with pre-computed hash
#[derive(Debug, Clone)]
struct TermEntry {
    term: TermData,
    sort: Sort,
}

/// The actual term data
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TermData {
    /// A constant value
    Const(Constant),
    /// A variable with name and unique ID
    Var(String, u32),
    /// Function application: function symbol + arguments
    App(Symbol, Vec<TermId>),
    /// Let binding (after expansion this should not appear)
    Let(Vec<(String, TermId)>, TermId),
    /// Negation (special case for efficient handling)
    Not(TermId),
    /// If-then-else
    Ite(TermId, TermId, TermId),
    /// Universal quantifier: forall ((x1 S1) (x2 S2) ...) body
    ///
    /// Triggers are multi-patterns:
    /// - Outer Vec = alternative trigger sets (disjunction)
    /// - Inner Vec = multi-trigger patterns (conjunction; currently flattened by E-matching)
    Forall(Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>),
    /// Existential quantifier: exists ((x1 S1) (x2 S2) ...) body
    ///
    /// Triggers are multi-patterns:
    /// - Outer Vec = alternative trigger sets (disjunction)
    /// - Inner Vec = multi-trigger patterns (conjunction; currently flattened by E-matching)
    Exists(Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>),
}

impl Hash for TermData {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Const(c) => c.hash(state),
            Self::Var(name, id) => {
                name.hash(state);
                id.hash(state);
            }
            Self::App(sym, args) => {
                sym.hash(state);
                args.hash(state);
            }
            Self::Let(bindings, body) => {
                bindings.hash(state);
                body.hash(state);
            }
            Self::Not(t) => t.hash(state),
            Self::Ite(c, t, e) => {
                c.hash(state);
                t.hash(state);
                e.hash(state);
            }
            Self::Forall(vars, body, triggers) | Self::Exists(vars, body, triggers) => {
                for (name, sort) in vars {
                    name.hash(state);
                    sort.hash(state);
                }
                body.hash(state);
                triggers.hash(state);
            }
        }
    }
}

/// Function/predicate symbol
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Symbol {
    /// Named function (user-defined or built-in)
    Named(String),
    /// Indexed function like (_ extract 7 4)
    Indexed(String, Vec<u32>),
}

impl Symbol {
    /// Create a named symbol
    pub fn named(name: impl Into<String>) -> Self {
        Self::Named(name.into())
    }

    /// Create an indexed symbol
    pub fn indexed(name: impl Into<String>, indices: Vec<u32>) -> Self {
        Self::Indexed(name.into(), indices)
    }

    /// Get the name of the symbol
    pub fn name(&self) -> &str {
        match self {
            Self::Named(n) | Self::Indexed(n, _) => n,
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Named(n) => write!(f, "{n}"),
            Self::Indexed(n, indices) => {
                write!(f, "(_ {n}")?;
                for idx in indices {
                    write!(f, " {idx}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Constant values
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Constant {
    /// Boolean constant
    Bool(bool),
    /// Integer constant (arbitrary precision)
    Int(BigInt),
    /// Rational constant
    Rational(RationalWrapper),
    /// Bitvector constant with value and width
    BitVec {
        /// The numeric value of the bitvector
        value: BigInt,
        /// The bit width of the bitvector
        width: u32,
    },
    /// String constant
    String(String),
}

/// Wrapper for BigRational to implement Eq and Hash
#[derive(Debug, Clone)]
pub struct RationalWrapper(pub BigRational);

impl PartialEq for RationalWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for RationalWrapper {}

impl Hash for RationalWrapper {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the normalized form
        self.0.numer().hash(state);
        self.0.denom().hash(state);
    }
}

impl From<BigRational> for RationalWrapper {
    fn from(r: BigRational) -> Self {
        Self(r)
    }
}

/// Hash-consing term store
///
/// All terms are stored uniquely. Creating a term that already exists
/// returns the existing TermId.
pub struct TermStore {
    /// All terms, indexed by TermId
    terms: Vec<TermEntry>,
    /// Hash-cons map: hash -> list of term IDs with that hash
    hash_cons: KaniHashMap<u64, Vec<TermId>>,
    /// Variable counter for generating unique IDs
    var_counter: u32,
    /// Named constants/variables: name -> (TermId, Sort)
    names: KaniHashMap<String, (TermId, Sort)>,
    /// Pre-allocated common terms
    true_term: Option<TermId>,
    false_term: Option<TermId>,
    /// Per-instance term memory counter (bytes). Not shared across instances.
    /// Tracks approximate allocation for THIS TermStore only, enabling
    /// per-solver memory budgets without cross-instance interference (#6563).
    instance_term_bytes: usize,
}

impl Default for TermStore {
    fn default() -> Self {
        Self::new()
    }
}

/// SMT-LIB Euclidean remainder: always non-negative, satisfying 0 <= r < |b|.
///
/// Rust's `%` truncates toward zero, which can give negative remainders.
/// This function adjusts the result to match SMT-LIB semantics where
/// `a = b * (div a b) + (mod a b)` and `(mod a b) >= 0`.
pub(super) fn smt_euclid_rem(a: &BigInt, b: &BigInt) -> BigInt {
    let r = a % b;
    if r.is_negative() {
        r + b.abs()
    } else {
        r
    }
}

impl TermStore {
    /// Create a new empty term store
    pub fn new() -> Self {
        let mut store = Self {
            terms: Vec::new(),
            hash_cons: KaniHashMap::default(),
            var_counter: 0,
            names: KaniHashMap::default(),
            true_term: None,
            false_term: None,
            instance_term_bytes: 0,
        };
        // Pre-create true and false
        store.true_term = Some(store.mk_bool(true));
        store.false_term = Some(store.mk_bool(false));
        store
    }

    /// Kani-only constructor: creates an empty TermStore without pre-creating
    /// true/false terms. Avoids the `mk_bool()` → `hash_cons.insert()` path
    /// that triggers deep BTree symbolic exploration in CBMC (#6612).
    ///
    /// Only suitable for Kani proofs that test pointer/structural properties
    /// without dereferencing term data.
    #[cfg(kani)]
    pub fn new_kani_minimal() -> Self {
        Self {
            terms: Vec::new(),
            hash_cons: KaniHashMap::default(),
            var_counter: 0,
            names: KaniHashMap::default(),
            true_term: None,
            false_term: None,
            instance_term_bytes: 0,
        }
    }

    /// Get the number of terms in the store
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Check if the store is empty
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    /// Iterator over all TermIds in this store.
    pub fn term_ids(&self) -> impl Iterator<Item = TermId> {
        (0..self.terms.len() as u32).map(TermId)
    }

    /// Check if aggregate term memory across all TermStore instances exceeds the budget,
    /// OR if the process-wide RSS limit has been exceeded.
    ///
    /// This is a cross-engine check: each portfolio engine has its own TermStore,
    /// but they all contribute to the same global counter. When the total exceeds
    /// the limit (default 4 GB), engines should stop and return Unknown.
    ///
    /// Also checks `z4_sys::process_memory_exceeded()` to catch overall process
    /// memory growth from non-term allocations (clause arenas, caches, etc.).
    ///
    /// The check uses `Relaxed` ordering — the exact byte count doesn't need to be
    /// precise, we just need to detect when we're in the danger zone.
    pub fn global_memory_exceeded() -> bool {
        GLOBAL_TERM_BYTES.load(Ordering::Relaxed) > DEFAULT_TERM_MEMORY_LIMIT
            || z4_sys::process_memory_exceeded()
    }

    /// Get the current global term memory usage in bytes (approximate).
    pub fn global_term_bytes() -> usize {
        GLOBAL_TERM_BYTES.load(Ordering::Relaxed)
    }

    /// Reset the global term memory counter.
    ///
    /// Call this at the start of a new portfolio solve to avoid accumulating
    /// counts from previous solves. Safe to call from any thread — the counter
    /// is atomic.
    pub fn reset_global_term_bytes() {
        GLOBAL_TERM_BYTES.store(0, Ordering::Relaxed);
    }

    /// Test-only helper to force the global term-byte counter.
    ///
    /// This is used by CHC regression tests to exercise memory-budget exit paths
    /// without allocating gigabytes of terms.
    #[doc(hidden)]
    pub fn force_global_term_bytes_for_testing(bytes: usize) {
        GLOBAL_TERM_BYTES.store(bytes, Ordering::Relaxed);
    }

    /// Per-instance term memory usage in bytes (approximate).
    ///
    /// Unlike `global_term_bytes()`, this counts only terms interned by THIS
    /// `TermStore` instance. Use this for per-solver memory budgets that must
    /// not interfere with other concurrent solver instances (#6563).
    pub fn instance_term_bytes(&self) -> usize {
        self.instance_term_bytes
    }

    /// Check if THIS instance has exceeded a given memory budget.
    pub fn instance_memory_exceeded(&self, limit: usize) -> bool {
        self.instance_term_bytes > limit
    }

    /// Get the TermId for true
    pub fn true_term(&self) -> TermId {
        self.true_term
            .expect("TermStore: true_term accessed before initialization")
    }

    /// Get the TermId for false
    pub fn false_term(&self) -> TermId {
        self.false_term
            .expect("TermStore: false_term accessed before initialization")
    }

    /// Get the term data for a TermId
    pub fn get(&self, id: TermId) -> &TermData {
        &self.terms[id.index()].term
    }

    /// Get the sort of a term
    pub fn sort(&self, id: TermId) -> &Sort {
        &self.terms[id.index()].sort
    }

    /// Compute hash for term data
    fn compute_hash(term: &TermData) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        term.hash(&mut hasher);
        hasher.finish()
    }

    /// Look up an existing term without creating a new interned entry.
    pub fn find_interned(&self, term: &TermData) -> Option<TermId> {
        let hash = Self::compute_hash(term);
        let ids = self.hash_cons.get(&hash)?;
        ids.iter()
            .copied()
            .find(|&id| &self.terms[id.index()].term == term)
    }

    /// Look up an existing equality term without triggering `mk_eq`
    /// simplification or allocating a fresh node.
    pub fn find_eq(&self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        if lhs == rhs {
            return Some(
                self.true_term
                    .expect("TermStore: true_term accessed before initialization"),
            );
        }
        let (a, b) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
        self.find_interned(&TermData::App(Symbol::named("="), vec![a, b]))
    }
}

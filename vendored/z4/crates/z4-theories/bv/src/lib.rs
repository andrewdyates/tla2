// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 BV - Bitvector theory solver
//!
//! Implements eager bit-blasting for bitvectors. Each bitvector variable is
//! mapped to a vector of boolean variables (one per bit), and bitvector
//! operations are translated to boolean circuits.

#![warn(missing_docs)]
#![warn(clippy::all)]

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

mod arithmetic;
mod arithmetic_ops;
mod assertions;
mod bitblast_bool;
mod comparisons;
mod delayed;
mod delayed_solver;
mod division;
mod gates;
mod shifts;
mod state;
mod theory_impl;

use std::sync::OnceLock;

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use z4_core::{CnfClause, CnfLit, Sort, TheoryPropagation, TheoryResult, TheorySolver};

pub use delayed::{DelayedBvOp, DelayedBvState};

/// Red zone size for `stacker::maybe_grow` in BV bitblasting.
const BV_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for BV bitblast recursion.
const BV_STACK_SIZE: usize = 2 * 1024 * 1024;

/// Cached `Z4_DUMP_BV_CNF` env var path (checked once per process).
fn dump_bv_cnf_path() -> Option<&'static String> {
    static CACHED: OnceLock<Option<String>> = OnceLock::new();
    CACHED
        .get_or_init(|| std::env::var("Z4_DUMP_BV_CNF").ok())
        .as_ref()
}

/// Cached `Z4_DEBUG_BOOL_ITE` env var (checked once per process).
/// Also enabled by `Z4_DEBUG_THEORY=1` umbrella.
fn debug_bool_ite() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("Z4_DEBUG_BOOL_ITE").is_ok() || std::env::var("Z4_DEBUG_THEORY").is_ok()
    })
}

/// A vector of boolean literals representing a bitvector
/// LSB is at index 0
pub type BvBits = Vec<CnfLit>;

/// Gate cache type: maps normalized `(min(a,b), max(a,b))` key to output literal.
pub type GateCache = HashMap<(CnfLit, CnfLit), CnfLit>;

/// Model extracted from BV solver with variable assignments
#[derive(Debug, Clone)]
pub struct BvModel {
    /// Variable assignments: term_id -> bitvector value (as BigInt)
    pub values: HashMap<TermId, num_bigint::BigInt>,
    /// Term to bit mappings (for debugging)
    pub term_to_bits: HashMap<TermId, BvBits>,
    /// Bool-sorted variable overrides from preprocessing substitution recovery.
    /// When a Bool variable is substituted with a BV predicate (e.g., `p -> (bvult x #x42)`),
    /// the evaluated Bool result is stored here for model validation (#5524).
    pub bool_overrides: HashMap<TermId, bool>,
}

/// Bitvector theory solver using eager bit-blasting
pub struct BvSolver<'a> {
    /// Reference to the term store
    terms: &'a TermStore,
    /// Mapping from BV term IDs to their bit representations
    term_to_bits: HashMap<TermId, BvBits>,
    /// Mapping from BV predicate term IDs to their bitblasted CNF variable
    /// This is used to connect Tseitin variables to BV bitblast results (#858)
    predicate_to_var: HashMap<TermId, CnfLit>,
    /// Mapping from Bool term IDs to their CNF variable.
    ///
    /// Used for bit-blasting Boolean conditions inside BV terms (e.g., `ite`).
    bool_to_var: HashMap<TermId, CnfLit>,
    /// Generated CNF clauses
    clauses: Vec<CnfClause>,
    /// Next fresh variable (1-indexed for DIMACS compatibility)
    next_var: u32,
    /// Trail of assertions for backtracking
    trail: Vec<TermId>,
    /// Stack of trail sizes for push/pop
    trail_stack: Vec<usize>,
    /// Asserted literals and their values
    asserted: HashMap<TermId, bool>,
    /// Bool terms that are conditions for BV-sorted ITE expressions.
    ///
    /// These are the ONLY Bool terms that should be linked via Tseitin
    /// equivalences. Linking all Bool terms is unsound because assertion-level
    /// structure (from `process_assertion`) creates incorrect equivalences
    /// that allow spurious SAT models. See #1696.
    bv_ite_conditions: HashSet<TermId>,
    /// Literals known to be false (constrained by unit clause `-lit`).
    /// Used for leading-zero optimization in multiplication. (#1720)
    known_false: HashSet<CnfLit>,
    /// Cached false literal: reused across all calls to `fresh_false()`.
    /// Avoids allocating a new variable and unit clause for every zero bit,
    /// which was a major source of variable bloat in QF_ABV benchmarks.
    cached_false_lit: Option<CnfLit>,
    /// Cached true literal: reused across all calls to `fresh_true()`.
    #[allow(dead_code)]
    cached_true_lit: Option<CnfLit>,
    /// Cache for AND gates: (min(a,b), max(a,b)) -> output literal
    /// Used for structural hashing to avoid duplicate gates. (#1774)
    and_cache: HashMap<(CnfLit, CnfLit), CnfLit>,
    /// Cache for OR gates: (min(a,b), max(a,b)) -> output literal
    /// Used for structural hashing to avoid duplicate gates. (#1774)
    or_cache: HashMap<(CnfLit, CnfLit), CnfLit>,
    /// Cache for XOR gates: (min(a,b), max(a,b)) -> output literal
    /// Used for structural hashing to avoid duplicate gates. (#1774)
    xor_cache: HashMap<(CnfLit, CnfLit), CnfLit>,
    /// Cache for unsigned division/remainder circuits (#4873).
    /// When both `bvudiv(x,y)` and `bvurem(x,y)` appear, they share one
    /// `bitblast_udiv_urem` circuit instead of building two independent ones.
    unsigned_div_cache: HashMap<(TermId, TermId), (BvBits, BvBits)>,
    /// Cache for signed division/remainder intermediates (#4873).
    /// Shares abs-value computation and unsigned division circuit between
    /// `bvsdiv(x,y)` and `bvsrem(x,y)`.  Stores (abs_q, abs_r, sign_a, sign_b).
    signed_div_cache: HashMap<(TermId, TermId), (BvBits, BvBits, CnfLit, CnfLit)>,
    /// Delayed operations: terms whose circuits are not yet built (#7015).
    /// Maps each delayed term to its operation name and argument TermIds.
    /// Fresh bits are allocated but unconstrained; the relationship between
    /// inputs and output is enforced lazily via `check_delayed_operations()`.
    delayed_ops: Vec<DelayedBvOp>,
    /// Whether delayed internalization is enabled for this BvSolver instance.
    delay_enabled: bool,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
}

impl<'a> BvSolver<'a> {
    /// Create a new BV solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        BvSolver {
            terms,
            term_to_bits: HashMap::new(),
            predicate_to_var: HashMap::new(),
            bool_to_var: HashMap::new(),
            clauses: Vec::new(),
            next_var: 1,
            trail: Vec::new(),
            trail_stack: Vec::new(),
            asserted: HashMap::new(),
            bv_ite_conditions: HashSet::new(),
            known_false: HashSet::new(),
            cached_false_lit: None,
            cached_true_lit: None,
            and_cache: HashMap::new(),
            or_cache: HashMap::new(),
            xor_cache: HashMap::new(),
            unsigned_div_cache: HashMap::new(),
            signed_div_cache: HashMap::new(),
            delayed_ops: Vec::new(),
            delay_enabled: false,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        }
    }

    /// Allocate a fresh CNF variable
    fn fresh_var(&mut self) -> CnfLit {
        let var = self.next_var as CnfLit;
        self.next_var += 1;
        var
    }

    /// Add a clause
    fn add_clause(&mut self, clause: CnfClause) {
        self.clauses.push(clause);
    }

    /// Dump CNF clauses in DIMACS format for debugging (#1708, #1816)
    fn dump_cnf_dimacs(&self, path: &str) {
        use std::io::Write;
        let mut file = match std::fs::File::create(path) {
            Ok(f) => f,
            Err(e) => {
                safe_eprintln!("[dump_cnf] Failed to create {}: {}", path, e);
                return;
            }
        };

        let num_vars = self.next_var - 1;
        let num_clauses = self.clauses.len();

        writeln!(file, "c Z4 BV bitblaster CNF dump").ok();
        writeln!(file, "c Variables: {num_vars}").ok();
        writeln!(file, "c Clauses: {num_clauses}").ok();
        writeln!(file, "p cnf {num_vars} {num_clauses}").ok();

        for clause in &self.clauses {
            let lits: Vec<String> = clause.literals().iter().map(ToString::to_string).collect();
            writeln!(file, "{} 0", lits.join(" ")).ok();
        }

        safe_eprintln!("[dump_cnf] Wrote {} clauses to {}", num_clauses, path);
    }

    /// Allocate a fresh CNF variable constrained to false.
    /// The literal is tracked in `known_false` for optimization. (#1720)
    /// Cached: all zero bits share a single variable to avoid CNF bloat.
    fn fresh_false(&mut self) -> CnfLit {
        if let Some(lit) = self.cached_false_lit {
            return lit;
        }
        let var = self.fresh_var();
        self.add_clause(CnfClause::unit(-var));
        self.known_false.insert(var);
        self.cached_false_lit = Some(var);
        var
    }

    /// Check if a literal is known to be false (i.e., constrained to false)
    fn is_known_false(&self, lit: CnfLit) -> bool {
        lit > 0 && self.known_false.contains(&lit)
    }

    /// Check if a literal is known to be true (i.e., constrained to true)
    fn is_known_true(&self, lit: CnfLit) -> bool {
        lit < 0 && self.known_false.contains(&-lit)
    }

    /// Check if a literal is a known constant (either true or false)
    fn is_known_const(&self, lit: CnfLit) -> bool {
        self.is_known_true(lit) || self.is_known_false(lit)
    }

    /// Create a fresh literal constrained to true.
    ///
    /// Returns a negative literal -v where v is in known_false, so
    /// is_known_true(-v) returns true.
    fn fresh_true(&mut self) -> CnfLit {
        let v = self.fresh_var();
        // Add v to known_false, then return -v
        // is_known_true(-v) = -v < 0 && known_false.contains(&-(-v)) = known_false.contains(&v)
        self.known_false.insert(v);
        // Add unit clause asserting v is false (which means -v is true)
        self.add_clause(CnfClause::unit(-v));
        -v
    }

    /// Get or create bit representation for a BV term.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    fn get_bits(&mut self, term: TermId) -> BvBits {
        stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, || {
            if let Some(bits) = self.term_to_bits.get(&term) {
                return bits.clone();
            }

            let bits = self.bitblast(term);
            self.term_to_bits.insert(term, bits.clone());
            bits
        })
    }

    /// Bit-blast a bitvector term
    fn bitblast(&mut self, term: TermId) -> BvBits {
        let data = self.terms.get(term).clone();

        match data {
            TermData::Const(Constant::BitVec { ref value, width }) => {
                // Constant: create bits from value.
                // Zero bits use `fresh_false` to track in `known_false` for multiplication
                // optimization (#1720).
                let mut bits = Vec::with_capacity(width as usize);
                for i in 0..width {
                    let bit_set =
                        (value >> i) & num_bigint::BigInt::from(1) != num_bigint::BigInt::from(0);
                    let lit = if bit_set {
                        let v = self.fresh_var();
                        self.add_clause(CnfClause::unit(v));
                        v
                    } else {
                        self.fresh_false()
                    };
                    bits.push(lit);
                }
                bits
            }
            TermData::Var(ref _name, _) => {
                // Variable: allocate fresh boolean variables
                let width = match self.terms.sort(term) {
                    Sort::BitVec(bv) => bv.width,
                    _ => return Vec::new(),
                };
                let mut bits = Vec::with_capacity(width as usize);
                for _ in 0..width {
                    bits.push(self.fresh_var());
                }
                bits
            }
            TermData::Ite(cond, then_term, else_term) => {
                let Sort::BitVec(_) = self.terms.sort(term) else {
                    return Vec::new();
                };
                // Track this condition as a BV ITE condition for Tseitin linking (#1696)
                self.bv_ite_conditions.insert(cond);
                let sel = self.bitblast_bool(cond);
                let t_bits = self.get_bits(then_term);
                let e_bits = self.get_bits(else_term);
                self.bitwise_mux(&t_bits, &e_bits, sel)
            }
            TermData::App(ref sym, ref args) => self.bitblast_app(term, sym, args),
            _ => {
                // Unknown term type - allocate fresh bits
                if let Sort::BitVec(bv) = self.terms.sort(term) {
                    let mut bits = Vec::with_capacity(bv.width as usize);
                    for _ in 0..bv.width {
                        bits.push(self.fresh_var());
                    }
                    bits
                } else {
                    Vec::new()
                }
            }
        }
    }

    /// Return fresh unconstrained bits for the given term's sort width.
    /// Used as fallback when bitblasting encounters width mismatches (#5595).
    fn fresh_bits_for_term(&mut self, term: TermId) -> BvBits {
        if let Sort::BitVec(bv) = self.terms.sort(term) {
            (0..bv.width).map(|_| self.fresh_var()).collect()
        } else {
            Vec::new()
        }
    }

    /// Get bits for a binary BV operation, returning None if operands have
    /// mismatched widths (0 bits from non-BV sub-terms). (#5595)
    fn get_binary_bits(&mut self, a: TermId, b: TermId) -> Option<(BvBits, BvBits)> {
        let a_bits = self.get_bits(a);
        let b_bits = self.get_bits(b);
        if a_bits.is_empty() || b_bits.is_empty() || a_bits.len() != b_bits.len() {
            None
        } else {
            Some((a_bits, b_bits))
        }
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;

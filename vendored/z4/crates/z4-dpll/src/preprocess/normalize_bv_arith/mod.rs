// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV arithmetic normalization preprocessing pass
//!
//! Canonicalizes commutative and associative BV operations (`bvadd`, `bvmul`,
//! `bvand`, `bvor`, `bvxor`) to improve term sharing and reduce CNF size
//! after bit-blasting.
//!
//! # Normalization
//!
//! For commutative+associative BV ops (`bvadd`, `bvmul`, `bvand`, `bvor`, `bvxor`):
//! 1. Flatten nested same-op trees into operand list
//! 2. Sort operands by TermId (deterministic ordering)
//! 3. Rebuild as left-associated binary tree (preserves binary arity)
//!
//! This ensures that syntactically different but semantically equivalent
//! expressions (e.g., `(bvadd a b)` vs `(bvadd b a)`) normalize to the
//! same canonical form.
//!
//! Note: Non-commutative ops like `bvsub`, `bvudiv`, `bvsdiv` are NOT normalized.
//!
//! # Reference
//!
//! Modeled after Bitwuzla's `PassNormalize` with Z4 extensions for bitwise ops:
//! - `reference/bitwuzla/src/preprocess/pass/normalize.cpp`
//! - Design: `designs/2026-02-01-bv-arithmetic-normalization-pass.md`

use super::PreprocessingPass;
#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermData;
use z4_core::{Sort, TermId, TermStore};

/// Check if a BV operation is commutative and associative (normalizable).
fn is_commutative_bv_op(name: &str) -> bool {
    matches!(name, "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor")
}

/// Normalizes BV arithmetic expressions for canonical form.
pub(crate) struct NormalizeBvArith {
    /// Cache: original term -> normalized term
    cache: HashMap<TermId, TermId>,
}

impl NormalizeBvArith {
    /// Create a new BV arithmetic normalization pass.
    pub(crate) fn new() -> Self {
        Self {
            cache: HashMap::new(),
        }
    }

    /// Normalize a term recursively, returning the normalized TermId.
    fn normalize(&mut self, terms: &mut TermStore, id: TermId) -> TermId {
        // Check cache first
        if let Some(&cached) = self.cache.get(&id) {
            return cached;
        }

        let result = match terms.get(id).clone() {
            TermData::App(sym, args) => {
                let name = sym.name();

                // Recursively normalize children first
                let normalized_args: Vec<TermId> =
                    args.iter().map(|&a| self.normalize(terms, a)).collect();

                // Check if this is a commutative+associative BV op
                if is_commutative_bv_op(name) {
                    // Flatten and canonicalize
                    let mut operands = Vec::new();
                    Self::flatten_op(terms, name, &normalized_args, &mut operands);

                    // Sort by TermId for canonical ordering
                    operands.sort_by_key(|t| t.index());

                    // Get width from first operand
                    let width = match terms.sort(operands[0]) {
                        Sort::BitVec(bv) => bv.width,
                        _ => return id, // Not a BV term, shouldn't happen
                    };

                    // Rebuild as left-associated binary tree
                    self.rebuild_binary_tree(terms, name, operands, width)
                } else {
                    // Not a commutative BV op: rebuild with normalized children
                    if normalized_args == args {
                        id // No change
                    } else {
                        self.rebuild_app(terms, id, sym, normalized_args)
                    }
                }
            }
            // Non-application terms: no normalization needed
            _ => id,
        };

        self.cache.insert(id, result);
        result
    }

    /// Flatten nested operations of the same kind into a flat operand list.
    fn flatten_op(terms: &TermStore, op_name: &str, args: &[TermId], operands: &mut Vec<TermId>) {
        for &arg in args {
            // Check if arg is the same operation
            if let TermData::App(sym, child_args) = terms.get(arg) {
                if sym.name() == op_name {
                    // Recursively flatten
                    Self::flatten_op(terms, op_name, child_args, operands);
                    continue;
                }
            }
            // Not same op: add as operand
            operands.push(arg);
        }
    }

    /// Rebuild a flat operand list as a left-associated binary tree.
    fn rebuild_binary_tree(
        &self,
        terms: &mut TermStore,
        op_name: &str,
        operands: Vec<TermId>,
        width: u32,
    ) -> TermId {
        debug_assert!(
            !operands.is_empty(),
            "BUG: empty operands in rebuild_binary_tree"
        );

        if operands.len() == 1 {
            return operands[0];
        }

        // Build left-associated: ((a + b) + c) + d
        let mut result = operands[0];
        for &operand in &operands[1..] {
            result = match op_name {
                "bvadd" => terms.mk_bvadd(vec![result, operand]),
                "bvmul" => terms.mk_bvmul(vec![result, operand]),
                "bvand" => terms.mk_bvand(vec![result, operand]),
                "bvor" => terms.mk_bvor(vec![result, operand]),
                "bvxor" => terms.mk_bvxor(vec![result, operand]),
                _ => unreachable!("BUG: unknown commutative BV op: {}", op_name),
            };

            // Verify width is preserved
            debug_assert!(
                matches!(terms.sort(result), Sort::BitVec(bv) if bv.width == width),
                "BUG: width changed during rebuild"
            );
        }

        result
    }

    /// Rebuild an application term with new arguments.
    fn rebuild_app(
        &self,
        terms: &mut TermStore,
        original: TermId,
        sym: z4_core::Symbol,
        args: Vec<TermId>,
    ) -> TermId {
        // Use TermStore's existing mk_* methods when available for simplification
        let name = sym.name();
        match name {
            // Binary BV ops
            "bvadd" => terms.mk_bvadd(args),
            "bvmul" => terms.mk_bvmul(args),
            "bvand" => terms.mk_bvand(args),
            "bvor" => terms.mk_bvor(args),
            "bvxor" => terms.mk_bvxor(args),
            // Unary BV ops
            "bvneg" if args.len() == 1 => terms.mk_bvneg(args[0]),
            "bvnot" if args.len() == 1 => terms.mk_bvnot(args[0]),
            // Boolean ops
            "and" => terms.mk_and(args),
            "or" => terms.mk_or(args),
            "not" if args.len() == 1 => terms.mk_not(args[0]),
            "ite" if args.len() == 3 => terms.mk_ite(args[0], args[1], args[2]),
            "eq" | "=" if args.len() == 2 => terms.mk_eq(args[0], args[1]),
            _ => {
                // Generic rebuild using public mk_app
                terms.mk_app(sym, args, terms.sort(original).clone())
            }
        }
    }
}

impl Default for NormalizeBvArith {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for NormalizeBvArith {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let mut modified = false;

        for assertion in assertions.iter_mut() {
            let normalized = self.normalize(terms, *assertion);
            if normalized != *assertion {
                *assertion = normalized;
                modified = true;
            }
        }

        modified
    }

    fn reset(&mut self) {
        self.cache.clear();
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

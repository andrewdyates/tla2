// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deep-tree drop safety for ChcExpr.

use std::sync::Arc;

use super::ChcExpr;

impl ChcExpr {
    /// Iteratively drop a `ChcExpr` tree to prevent stack overflow.
    ///
    /// The default recursive drop uses O(depth) stack frames. For deeply nested
    /// trees (e.g., right-skewed chains of 10K+ nodes), this overflows the stack.
    /// This function uses a worklist to flatten the drop into O(1) stack space.
    ///
    /// Only uniquely-owned `Arc` children (strong_count == 1) are unwrapped and
    /// added to the worklist. Shared Arcs simply have their refcount decremented.
    ///
    /// # When to use
    ///
    /// Call this instead of `drop(expr)` for expressions that may be deeply nested
    /// (e.g., after building deep test trees, or when tearing down solver state
    /// with potentially deep conjunction/disjunction chains).
    ///
    /// Note: `impl Drop for ChcExpr` is intentionally NOT used because Rust
    /// prevents pattern-matching moves from types that implement Drop, which
    /// would break 15+ match sites across the codebase.
    pub fn iterative_drop(mut root: Self) {
        let mut worklist: Vec<Self> = Vec::new();
        Self::extract_children_for_drop(&mut root, &mut worklist);
        // root drops here as a leaf (children drained), no recursion
        drop(root);
        while let Some(mut node) = worklist.pop() {
            Self::extract_children_for_drop(&mut node, &mut worklist);
            // node drops here as a leaf, no recursion
        }
    }

    /// Extract uniquely-owned children from `node` into `worklist`, leaving
    /// `node` as a childless shell that can be dropped without recursion.
    fn extract_children_for_drop(node: &mut Self, worklist: &mut Vec<Self>) {
        match node {
            Self::Op(_, children)
            | Self::PredicateApp(_, _, children)
            | Self::FuncApp(_, _, children) => {
                for arc in children.drain(..) {
                    if let Ok(inner) = Arc::try_unwrap(arc) {
                        worklist.push(inner);
                    }
                    // else: shared Arc, refcount decremented, no deep recursion
                }
            }
            Self::ConstArray(_ks, arc) => {
                let taken = std::mem::replace(arc, Arc::new(Self::Bool(false)));
                if let Ok(inner) = Arc::try_unwrap(taken) {
                    worklist.push(inner);
                }
            }
            Self::Bool(_)
            | Self::Int(_)
            | Self::Real(_, _)
            | Self::BitVec(_, _)
            | Self::Var(_)
            | Self::ConstArrayMarker(_)
            | Self::IsTesterMarker(_) => {}
        }
    }
}

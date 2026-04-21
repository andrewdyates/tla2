// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term classification helpers for model validation.
//!
//! Contains methods on `Executor` for classifying terms: internal symbols,
//! datatype content, quantifiers, array operations, term flag precomputation, etc.
//!
//! Extracted from `validation.rs` as part of the code-health module split.

use z4_core::term::{Constant, TermData};
use z4_core::{Sort, TermId};

use super::{
    TERM_FLAG_ARRAY, TERM_FLAG_BV_CMP, TERM_FLAG_DATATYPE, TERM_FLAG_INTERNAL,
    TERM_FLAG_QUANTIFIER, TERM_FLAG_SEQ, TERM_FLAG_STRING,
};
use crate::executor::model::{Executor, Model, EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE};

impl Executor {
    /// Check whether a term tree contains an internal encoding symbol.
    /// Internal symbols (`__z4_*`) are auxiliary encoding artifacts and are
    /// excluded from top-level model validation.
    pub(in crate::executor::model) fn contains_internal_symbol(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__z4_") {
                        return true;
                    }
                    args.iter().any(|&arg| self.contains_internal_symbol(arg))
                }
                TermData::Not(inner) => self.contains_internal_symbol(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_internal_symbol(*c)
                        || self.contains_internal_symbol(*t)
                        || self.contains_internal_symbol(*e)
                }
                TermData::Let(_, body) => self.contains_internal_symbol(*body),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_internal_symbol(*body)
                }
                TermData::Const(_) | TermData::Var(_, _) => false,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!(
                    "unhandled TermData variant in contains_internal_symbol(): {other:?}"
                ),
            }
        })
    }

    /// Check whether a term is an equality between array-sorted operands.
    ///
    /// Array equalities like `(= a (store b i v))` are verified by the theory
    /// solver but may fail structural comparison in the model evaluator.
    #[allow(dead_code)]
    pub(crate) fn is_array_equality(&self, term_id: TermId) -> bool {
        if let TermData::App(sym, args) = self.ctx.terms.get(term_id) {
            if sym.name() == "=" && args.len() == 2 {
                return matches!(self.ctx.terms.sort(args[0]), Sort::Array(_));
            }
        }
        false
    }

    /// Check whether a term tree contains a datatype-sorted subterm.
    ///
    /// Datatype symbols may be represented via uninterpreted sorts in the term
    /// store, so this check also uses frontend datatype symbol metadata.
    pub(in crate::executor::model) fn contains_datatype_term(&self, term_id: TermId) -> bool {
        fn is_datatype_symbol_name(executor: &Executor, name: &str) -> bool {
            if executor.ctx.is_constructor(name).is_some() {
                return true;
            }
            if name
                .strip_prefix("is-")
                .is_some_and(|ctor| executor.ctx.is_constructor(ctor).is_some())
            {
                return true;
            }
            executor
                .ctx
                .ctor_selectors_iter()
                .any(|(_ctor, selectors)| selectors.iter().any(|sel| sel == name))
        }

        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            if self.ctx.terms.sort(term_id).is_datatype() {
                return true;
            }
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) => {
                    is_datatype_symbol_name(self, sym.name())
                        || args.iter().any(|&arg| self.contains_datatype_term(arg))
                }
                TermData::Not(inner) => self.contains_datatype_term(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_datatype_term(*c)
                        || self.contains_datatype_term(*t)
                        || self.contains_datatype_term(*e)
                }
                TermData::Let(_, body) => self.contains_datatype_term(*body),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_datatype_term(*body)
                }
                TermData::Var(name, _) => is_datatype_symbol_name(self, name),
                TermData::Const(_) => false,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!(
                    "unhandled TermData variant in contains_datatype_term(): {other:?}"
                ),
            }
        })
    }

    /// Flatten top-level conjunctions in the assertion list (#5585).
    ///
    /// The solve pipeline's `FlattenAnd` preprocessor splits conjunctions before
    /// Tseitin encoding, so individual conjuncts have SAT variable mappings but
    /// the parent conjunction node may not. This helper mirrors that flattening
    /// so `validate_model` can check each leaf assertion independently with its
    /// own term flags and SAT-fallback lookup.
    pub(crate) fn flatten_assertion_conjunctions(&self) -> Vec<TermId> {
        let mut result = Vec::with_capacity(self.ctx.assertions.len());
        let mut stack: Vec<TermId> = self.ctx.assertions.iter().rev().copied().collect();
        while let Some(term_id) = stack.pop() {
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) if sym.name() == "and" => {
                    // Push children in reverse so they come out in order
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
                _ => {
                    result.push(term_id);
                }
            }
        }
        result
    }

    /// Return whether an assertion is an arithmetic Boolean atom where a SAT
    /// truth assignment can be used as a conservative fallback when direct
    /// model evaluation is currently incomplete.
    pub(crate) fn is_arithmetic_boolean_assertion(&self, term_id: TermId) -> bool {
        let mut current = term_id;
        while let TermData::Not(inner) = self.ctx.terms.get(current) {
            current = *inner;
        }

        match self.ctx.terms.get(current) {
            TermData::App(sym, args) => match sym.name() {
                "<" | "<=" | ">" | ">=" => args.len() == 2,
                "=" | "distinct" if args.len() == 2 => {
                    matches!(self.ctx.terms.sort(args[0]), Sort::Int | Sort::Real)
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Whether a definitively-false arithmetic assertion could plausibly be a
    /// model-extraction gap instead of a hard semantic violation.
    ///
    /// This is intentionally narrower than the `Unknown` SAT-fallback path:
    /// ground arithmetic formulas like `(< 1 0)` must still validate as hard
    /// violations even if the SAT assignment says `true`.
    pub(in crate::executor::model) fn arithmetic_false_may_be_model_extraction_gap(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> bool {
        if !self.is_arithmetic_boolean_assertion(term_id) {
            return false;
        }
        if model.lia_model.is_none() && model.lra_model.is_none() {
            return false;
        }
        !self.validation_term_is_ground(term_id)
    }

    fn validation_term_is_ground(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Var(..)
                | TermData::Let(..)
                | TermData::Forall(..)
                | TermData::Exists(..) => false,
                TermData::Const(_) => true,
                TermData::App(_, args) => {
                    args.iter().all(|&arg| self.validation_term_is_ground(arg))
                }
                TermData::Not(inner) => self.validation_term_is_ground(*inner),
                TermData::Ite(c, t, e) => [*c, *t, *e]
                    .into_iter()
                    .all(|id| self.validation_term_is_ground(id)),
                other => unreachable!(
                    "unhandled TermData variant in validation_term_is_ground(): {other:?}"
                ),
            }
        })
    }

    /// Return whether a Bool assertion is purely propositional.
    ///
    /// These formulas are justified directly by the SAT assignment when the
    /// evaluator cannot reconstruct intermediate Bool variable values. This is
    /// narrower than SAT-fallback for theory atoms: only Bool vars/constants,
    /// Boolean connectives, Boolean equality, and Bool ITE are accepted.
    pub(in crate::executor::model) fn is_pure_boolean_formula(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            if *self.ctx.terms.sort(term_id) != Sort::Bool {
                return false;
            }

            match self.ctx.terms.get(term_id) {
                TermData::Const(Constant::Bool(_)) => true,
                TermData::Var(_, _) => true,
                TermData::Not(inner) => self.is_pure_boolean_formula(*inner),
                TermData::Ite(cond, then_br, else_br) => {
                    self.is_pure_boolean_formula(*cond)
                        && self.is_pure_boolean_formula(*then_br)
                        && self.is_pure_boolean_formula(*else_br)
                }
                TermData::App(sym, args) => match sym.name() {
                    "and" | "or" | "xor" => {
                        !args.is_empty()
                            && args.iter().all(|&arg| self.is_pure_boolean_formula(arg))
                    }
                    "=>" => {
                        args.len() == 2
                            && self.is_pure_boolean_formula(args[0])
                            && self.is_pure_boolean_formula(args[1])
                    }
                    "=" => {
                        args.len() == 2
                            && *self.ctx.terms.sort(args[0]) == Sort::Bool
                            && *self.ctx.terms.sort(args[1]) == Sort::Bool
                            && self.is_pure_boolean_formula(args[0])
                            && self.is_pure_boolean_formula(args[1])
                    }
                    _ => false,
                },
                TermData::Const(_)
                | TermData::Forall(_, _, _)
                | TermData::Exists(_, _, _)
                | TermData::Let(_, _) => false,
                other => {
                    unreachable!(
                        "unhandled TermData variant in is_pure_boolean_formula(): {other:?}"
                    )
                }
            }
        })
    }

    /// Check whether a term tree contains a quantifier (Forall or Exists).
    ///
    /// Quantified assertions cannot be model-checked; Unknown is acceptable
    /// for these assertions since the theory solvers already verified SAT.
    pub(in crate::executor::model) fn contains_quantifier(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => true,
                TermData::App(_, args) => args.iter().any(|&arg| self.contains_quantifier(arg)),
                TermData::Not(inner) => self.contains_quantifier(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_quantifier(*c)
                        || self.contains_quantifier(*t)
                        || self.contains_quantifier(*e)
                }
                TermData::Let(_, body) => self.contains_quantifier(*body),
                TermData::Const(_) | TermData::Var(_, _) => false,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => {
                    unreachable!("unhandled TermData variant in contains_quantifier(): {other:?}")
                }
            }
        })
    }

    /// Check whether a term contains an array operation (select, store,
    /// const-array) or a variable of Array sort.
    ///
    /// Used to classify validation diagnostics for array-containing assertions.
    #[cfg(test)]
    pub(in crate::executor::model) fn contains_array_term(&self, term_id: TermId) -> bool {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            match self.ctx.terms.get(term_id) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    if name == "select" || name == "store" || name == "const-array" {
                        return true;
                    }
                    args.iter().any(|&arg| self.contains_array_term(arg))
                }
                TermData::Var(_, _) => matches!(self.ctx.terms.sort(term_id), Sort::Array(_)),
                TermData::Not(inner) => self.contains_array_term(*inner),
                TermData::Ite(c, t, e) => {
                    self.contains_array_term(*c)
                        || self.contains_array_term(*t)
                        || self.contains_array_term(*e)
                }
                TermData::Let(_, body) => self.contains_array_term(*body),
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    self.contains_array_term(*body)
                }
                TermData::Const(_) => false,
                other => {
                    unreachable!("unhandled TermData variant in contains_array_term(): {other:?}")
                }
            }
        })
    }

    /// Precompute term classification flags for all terms in a single O(T) pass.
    ///
    /// Because TermIds are allocated sequentially and children always have lower
    /// IDs than parents, a single forward pass from 0..T propagates flags from
    /// children to parents correctly. This replaces 5 separate recursive tree
    /// walks per assertion in `validate_model`, avoiding exponential re-traversal
    /// on shared DAG subterms.
    pub(in crate::executor::model) fn precompute_term_flags(&self) -> Vec<u8> {
        let n = self.ctx.terms.len();
        let mut flags = vec![0u8; n];

        for idx in 0..n {
            let tid = TermId(idx as u32);
            let mut f = 0u8;

            match self.ctx.terms.get(tid) {
                TermData::App(sym, args) => {
                    let name = sym.name();
                    // Internal symbol check
                    if name.starts_with("__z4_") {
                        f |= TERM_FLAG_INTERNAL;
                    }
                    // Array term check
                    if name == "select" || name == "store" || name == "const-array" {
                        f |= TERM_FLAG_ARRAY;
                    }
                    // Seq term check (#5841, #5995): flag Seq operations for
                    // ground evaluation in validate_model.
                    if name.starts_with("seq.") {
                        f |= TERM_FLAG_SEQ;
                    }
                    // String operation check (#4057): flag str.* operations.
                    // String model extraction only assigns values from EQC
                    // constants and may not reflect computed string operations
                    // (str.substr, str.replace, etc.). Model validation
                    // Bool(false) on string assertions is unreliable.
                    if name.starts_with("str.") {
                        f |= TERM_FLAG_STRING;
                    }
                    // BV comparison check
                    if matches!(
                        name,
                        "bvult"
                            | "bvule"
                            | "bvugt"
                            | "bvuge"
                            | "bvslt"
                            | "bvsle"
                            | "bvsgt"
                            | "bvsge"
                    ) {
                        f |= TERM_FLAG_BV_CMP;
                    }
                    // BV equality check
                    if name == "="
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(args[0]), Sort::BitVec(_))
                    {
                        f |= TERM_FLAG_BV_CMP;
                    }
                    // Datatype symbol check (constructor, tester, selector)
                    if self.ctx.is_constructor(name).is_some()
                        || name
                            .strip_prefix("is-")
                            .is_some_and(|ctor| self.ctx.is_constructor(ctor).is_some())
                        || self
                            .ctx
                            .ctor_selectors_iter()
                            .any(|(_ctor, sels)| sels.iter().any(|sel| sel == name))
                    {
                        f |= TERM_FLAG_DATATYPE;
                    }
                    // Propagate children flags
                    for &arg in args {
                        f |= flags[arg.index()];
                    }
                }
                TermData::Var(name, _) => {
                    // Internal variable check: solver-generated Skolem witnesses
                    // (extensionality __ext_diff_*, store decomposition __z4_*)
                    // should be treated as internal for model validation (#6731).
                    if name.starts_with("__ext_diff_") || name.starts_with("__z4_") {
                        f |= TERM_FLAG_INTERNAL;
                    }
                    // Array-sorted variables
                    if matches!(self.ctx.terms.sort(tid), Sort::Array(_)) {
                        f |= TERM_FLAG_ARRAY;
                    }
                    // Seq-sorted variables (#5841)
                    if self.ctx.terms.sort(tid).is_seq() {
                        f |= TERM_FLAG_SEQ;
                    }
                    // String-sorted variables (#4057)
                    if matches!(self.ctx.terms.sort(tid), Sort::String) {
                        f |= TERM_FLAG_STRING;
                    }
                    // Datatype-sorted variables or DT symbol names.
                    // DT sorts are stored as Sort::Uninterpreted("<name>") internally,
                    // so we also check if the uninterpreted sort name matches a declared
                    // datatype (dt_axioms.rs:468-470 documents this representation).
                    if self.ctx.terms.sort(tid).is_datatype()
                        || matches!(
                            self.ctx.terms.sort(tid),
                            Sort::Uninterpreted(ref s) if self.ctx.datatype_iter().any(|(dt, _)| dt == s.as_str())
                        )
                        || self.ctx.is_constructor(name).is_some()
                        || name
                            .strip_prefix("is-")
                            .is_some_and(|ctor| self.ctx.is_constructor(ctor).is_some())
                        || self
                            .ctx
                            .ctor_selectors_iter()
                            .any(|(_ctor, sels)| sels.iter().any(|sel| sel == name.as_str()))
                    {
                        f |= TERM_FLAG_DATATYPE;
                    }
                }
                TermData::Not(inner) => {
                    f |= flags[inner.index()];
                }
                TermData::Ite(c, t, e) => {
                    f |= flags[c.index()] | flags[t.index()] | flags[e.index()];
                }
                TermData::Let(_, body) => {
                    f |= flags[body.index()];
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                    f |= TERM_FLAG_QUANTIFIER;
                    f |= flags[body.index()];
                }
                TermData::Const(_) => {
                    // Datatype sort on constants (including Uninterpreted representation)
                    if self.ctx.terms.sort(tid).is_datatype()
                        || matches!(
                            self.ctx.terms.sort(tid),
                            Sort::Uninterpreted(ref s) if self.ctx.datatype_iter().any(|(dt, _)| dt == s.as_str())
                        )
                    {
                        f |= TERM_FLAG_DATATYPE;
                    }
                }
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => {
                    unreachable!("unhandled TermData variant in precompute_term_flags(): {other:?}")
                }
            }

            flags[idx] = f;
        }

        flags
    }

    pub(in crate::executor::model) fn sat_term_assigned_true(
        &self,
        model: &Model,
        term: TermId,
    ) -> bool {
        self.term_value(&model.sat_model, &model.term_to_var, term)
            .is_some_and(|b| b)
    }

    pub(in crate::executor::model) fn sat_assumption_assigned_true(
        &self,
        model: &Model,
        assumption: TermId,
    ) -> bool {
        let has_sat_var = model
            .term_to_var
            .get(&assumption)
            .and_then(|&var_idx| model.sat_model.get(var_idx as usize))
            .copied()
            == Some(true);
        let has_negated_sat_var = if let TermData::Not(inner) = self.ctx.terms.get(assumption) {
            model
                .term_to_var
                .get(inner)
                .and_then(|&var_idx| model.sat_model.get(var_idx as usize))
                .copied()
                == Some(false)
        } else {
            false
        };
        has_sat_var || has_negated_sat_var
    }
}

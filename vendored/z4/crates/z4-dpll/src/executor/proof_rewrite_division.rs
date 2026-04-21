// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Auxiliary division variable analysis and demotion for proof rewriting.
//!
//! Identifies `_mod_q`/`_div_q`/`_mod_r`/`_div_r` auxiliary variables
//! introduced by the LIA division encoding, infers division term rewrites,
//! and demotes non-problem assumptions to `trust` steps.
//!
//! Extracted from `proof_rewrite.rs` for code health (#5970).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::Symbol;
use z4_core::term::TermData;
use z4_core::{AletheRule, Constant, Proof, ProofStep};
use z4_core::{TermId, TermStore};

use super::Executor;

impl Executor {
    pub(in crate::executor) fn collect_assume_steps_with_aux_mod_div_vars(
        terms: &TermStore,
        proof: &Proof,
    ) -> HashSet<u32> {
        let mut out = HashSet::new();
        for (idx, step) in proof.steps.iter().enumerate() {
            if let ProofStep::Assume(term) = step {
                if Self::term_contains_aux_mod_div_var(terms, *term) {
                    out.insert(idx as u32);
                }
            }
        }
        out
    }

    pub(in crate::executor) fn infer_auxiliary_division_rewrites(
        terms: &mut TermStore,
        proof: &Proof,
        rewrites: &mut HashMap<TermId, TermId>,
    ) {
        for step in &proof.steps {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            let Some((dividend, divisor, quotient, remainder)) =
                Self::parse_aux_division_constraint(terms, *term)
            else {
                continue;
            };
            let div_term = terms.mk_intdiv(dividend, divisor);
            let mod_term = terms.mk_mod(dividend, divisor);
            rewrites.insert(quotient, div_term);
            rewrites.insert(remainder, mod_term);
        }
    }

    fn parse_aux_division_constraint(
        terms: &mut TermStore,
        term: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let (lhs, rhs) = match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => return None,
        };
        Self::parse_aux_division_rhs(terms, lhs, rhs)
            .or_else(|| Self::parse_aux_division_rhs(terms, rhs, lhs))
    }

    fn parse_aux_division_rhs(
        terms: &mut TermStore,
        dividend: TermId,
        rhs: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let (lhs, rhs) = match terms.get(rhs) {
            TermData::App(Symbol::Named(name), args) if name == "+" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => return None,
        };
        Self::parse_aux_division_addend_pair(terms, dividend, lhs, rhs)
            .or_else(|| Self::parse_aux_division_addend_pair(terms, dividend, rhs, lhs))
    }

    fn parse_aux_division_addend_pair(
        terms: &mut TermStore,
        dividend: TermId,
        scaled_q: TermId,
        remainder: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let (divisor, quotient) = Self::parse_scaled_aux_quotient(terms, scaled_q)?;
        let remainder = Self::as_aux_remainder_var(terms, remainder)?;
        Some((dividend, divisor, quotient, remainder))
    }

    fn parse_scaled_aux_quotient(terms: &mut TermStore, term: TermId) -> Option<(TermId, TermId)> {
        if let Some(q) = Self::as_aux_quotient_var(terms, term) {
            return Some((terms.mk_int(BigInt::from(1)), q));
        }
        let (lhs, rhs) = match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "*" && args.len() == 2 => {
                (args[0], args[1])
            }
            _ => return None,
        };
        if Self::is_int_const_term(terms, lhs) {
            return Self::as_aux_quotient_var(terms, rhs).map(|q| (lhs, q));
        }
        if Self::is_int_const_term(terms, rhs) {
            return Self::as_aux_quotient_var(terms, lhs).map(|q| (rhs, q));
        }
        None
    }

    fn as_aux_quotient_var(terms: &TermStore, term: TermId) -> Option<TermId> {
        let TermData::Var(name, _) = terms.get(term) else {
            return None;
        };
        (name.starts_with("_mod_q") || name.starts_with("_div_q")).then_some(term)
    }

    fn as_aux_remainder_var(terms: &TermStore, term: TermId) -> Option<TermId> {
        let TermData::Var(name, _) = terms.get(term) else {
            return None;
        };
        (name.starts_with("_mod_r") || name.starts_with("_div_r")).then_some(term)
    }

    fn is_int_const_term(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Const(Constant::Int(_)))
    }

    pub(in crate::executor) fn demote_auxiliary_non_problem_assumptions(
        proof: &mut Proof,
        problem_assertions: &[TermId],
        aux_assume_steps: &HashSet<u32>,
    ) {
        if aux_assume_steps.is_empty() {
            return;
        }
        debug_assert!(
            aux_assume_steps
                .iter()
                .all(|&idx| (idx as usize) < proof.steps.len()),
            "BUG: aux_assume_steps contains index beyond proof.steps.len() ({})",
            proof.steps.len()
        );
        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();
        for (idx, step) in proof.steps.iter_mut().enumerate() {
            if !aux_assume_steps.contains(&(idx as u32)) {
                continue;
            }
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if problem_set.contains(term) {
                continue;
            }
            *step = ProofStep::Step {
                rule: AletheRule::Trust,
                clause: vec![*term],
                premises: Vec::new(),
                args: Vec::new(),
            };
        }
    }

    pub(in crate::executor) fn demote_non_problem_assumptions(
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) {
        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();
        for step in &mut proof.steps {
            let ProofStep::Assume(term) = step else {
                continue;
            };
            if problem_set.contains(term) {
                continue;
            }
            *step = ProofStep::Step {
                rule: AletheRule::Trust,
                clause: vec![*term],
                premises: Vec::new(),
                args: Vec::new(),
            };
        }
    }

    pub(in crate::executor) fn term_contains_aux_mod_div_var(
        terms: &TermStore,
        root: TermId,
    ) -> bool {
        let mut stack = vec![root];
        let mut visited: HashSet<TermId> = HashSet::new();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::Var(name, _)
                    if name.starts_with("_mod_") || name.starts_with("_div_") =>
                {
                    return true
                }
                TermData::Const(_) => {}
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, trig) | TermData::Exists(_, body, trig) => {
                    stack.push(*body);
                    for m in trig {
                        stack.extend(m.iter().copied());
                    }
                }
                _ => {} // non_exhaustive catch-all
            }
        }
        false
    }
}

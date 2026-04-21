// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-BV EUF congruence axiom generation for combined BV theories.
//!
//! Handles congruence for UF applications whose return type is non-BV
//! (uninterpreted sorts, datatypes, Int, Bool, etc.) by connecting argument
//! equality to Tseitin variables rather than BV bit-level XOR encoding.
//!
//! Split from `bv_axioms_euf.rs` for code health (#5970).

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::TermId;

use super::super::Executor;

/// Result of attempting to build argument-difference SAT variables (#5457).
enum ArgDiffResult {
    /// All argument pairs are identical TermIds — outputs must be equivalent.
    AllIdentical,
    /// All different pairs have BV bits — conditional congruence with diff vars.
    Encoded(Vec<i32>),
    /// Some argument pairs differ but lack BV bits (e.g., DT-sorted) — cannot
    /// encode difference, so congruence must be skipped to avoid unsoundness.
    Unencodable,
}

impl Executor {
    /// Generate congruence axioms for UF applications with non-BV return types (#5433).
    ///
    /// The standard `generate_euf_bv_axioms_debug` handles only BV-return UFs (it
    /// needs BV bits for the result). For UFs returning uninterpreted sorts, datatypes,
    /// Int, etc., we connect argument equality to the Tseitin variable for the result
    /// equality term `(= f(a) f(b))`.
    ///
    /// Takes `term_bits` (a snapshot of `bv_solver.term_to_bits()`) to avoid borrow
    /// conflicts with `&mut self.ctx.terms` needed for `mk_eq`.
    ///
    /// Returns the number of fresh SAT variables allocated.
    pub(in crate::executor) fn generate_non_bv_euf_congruence(
        &mut self,
        term_bits: &HashMap<TermId, Vec<i32>>,
        tseitin_result: &z4_core::TseitinResult,
        var_offset: u32,
        all_clauses: &mut Vec<z4_core::CnfClause>,
        extra_terms: &[TermId],
    ) -> u32 {
        let mut uf_apps: HashMap<String, Vec<(TermId, Vec<TermId>)>> = HashMap::new();
        let mut visited = hashbrown::HashSet::new();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        let bv_offset = tseitin_result.num_vars;
        let mut next_var = var_offset + 1;

        for (_func_name, applications) in &uf_apps {
            if applications.len() < 2 {
                continue;
            }

            for i in 0..applications.len() {
                for j in (i + 1)..applications.len() {
                    let (term1, args1) = &applications[i];
                    let (term2, args2) = &applications[j];

                    if args1.len() != args2.len() {
                        continue;
                    }

                    // Skip pairs that generate_euf_bv_axioms_debug fully handles:
                    // both results AND all differing args have BV bits (#5439).
                    let has_bits1 = term_bits.contains_key(term1);
                    let has_bits2 = term_bits.contains_key(term2);
                    if has_bits1 && has_bits2 {
                        let all_args_bv = args1.iter().zip(args2.iter()).all(|(a1, a2)| {
                            a1 == a2 || (term_bits.contains_key(a1) && term_bits.contains_key(a2))
                        });
                        if all_args_bv {
                            continue;
                        }
                    }

                    // Pre-compute Tseitin literals for argument-pair equalities
                    // so build_arg_diff_vars can handle non-BV args (#5439).
                    let arg_eq_lits: Vec<Option<i32>> = args1
                        .iter()
                        .zip(args2.iter())
                        .map(|(&a1, &a2)| {
                            if a1 == a2 {
                                return None;
                            }
                            // Sort mismatch means args can never be equal (#2682).
                            if self.ctx.terms.sort(a1) != self.ctx.terms.sort(a2) {
                                return None;
                            }
                            let eq = self.ctx.terms.mk_eq(a1, a2);
                            if let Some(v) = tseitin_result.var_for_term(eq) {
                                Some(v as i32)
                            } else {
                                let not_eq = self.ctx.terms.mk_not(eq);
                                tseitin_result.var_for_term(not_eq).map(|v| -(v as i32))
                            }
                        })
                        .collect();

                    // Build argument-difference variables (once per pair)
                    let diff_result = Self::build_arg_diff_vars(
                        &mut self.ctx.terms,
                        args1,
                        args2,
                        term_bits,
                        tseitin_result,
                        bv_offset,
                        &arg_eq_lits,
                        &mut next_var,
                        all_clauses,
                    );

                    // If arguments differ but we can't encode the difference (e.g.,
                    // DT-sorted args with no BV bits), skip this congruence pair entirely.
                    // Generating unconditional congruence here is UNSOUND (#5457):
                    // e.g., is-SomeOpt(x) ↔ is-SomeOpt(NoneOpt) forced unconditionally
                    // creates false UNSAT when x ≠ NoneOpt.
                    if matches!(diff_result, ArgDiffResult::Unencodable) {
                        continue;
                    }

                    let diff_vars = match &diff_result {
                        ArgDiffResult::Encoded(v) => Some(v),
                        _ => None,
                    };

                    // 1. Equality atom congruence: find (= term1 term2) Tseitin var
                    let eq_term = self.ctx.terms.mk_eq(*term1, *term2);
                    if let Some(eq_tvar) = tseitin_result.var_for_term(eq_term) {
                        let eq_lit = eq_tvar as i32;
                        if let Some(diff_vars) = diff_vars {
                            // Congruence: (args_differ) ∨ (f(a) = f(b))
                            let mut clause = diff_vars.clone();
                            clause.push(eq_lit);
                            all_clauses.push(z4_core::CnfClause::new(clause));
                        } else {
                            // All args identical — equality must hold
                            all_clauses.push(z4_core::CnfClause::unit(eq_lit));
                        }
                    }
                    // No Tseitin variable for (= f(a) f(b)): skip equality atom
                    // congruence. Previously allocated an unconstrained fresh var
                    // which the SAT solver could freely set true, making the clause
                    // vacuous (#5439 Gap 2). Sections 1b (distinct) and 2 (Bool-return
                    // Tseitin) still enforce congruence where possible.

                    // 1b. Distinct atom congruence: find (distinct term1 term2)
                    // The old inline code handled both = and distinct; mk_eq only
                    // finds =. Without this, (distinct f(a) f(b)) loses congruence
                    // when f returns a non-BV sort.
                    let dist_term = self.ctx.terms.mk_distinct(vec![*term1, *term2]);
                    if let Some(dist_tvar) = tseitin_result.var_for_term(dist_term) {
                        let dist_lit = dist_tvar as i32;
                        if let Some(diff_vars) = diff_vars {
                            // Congruence: (args_differ) ∨ ¬(distinct f(a) f(b))
                            let mut clause = diff_vars.clone();
                            clause.push(-dist_lit);
                            all_clauses.push(z4_core::CnfClause::new(clause));
                        } else {
                            // All args identical — distinct must be false
                            all_clauses.push(z4_core::CnfClause::unit(-dist_lit));
                        }
                    }

                    // 2. Direct Tseitin variable congruence for Bool-return UFs (#5437)
                    // When f returns Bool, f(a) and f(b) have Tseitin variables directly
                    // but no explicit (= f(a) f(b)) atom. Encode: args same → tv1 ↔ tv2
                    let tvar1 = tseitin_result.var_for_term(*term1);
                    let tvar2 = tseitin_result.var_for_term(*term2);
                    if let (Some(tv1), Some(tv2)) = (tvar1, tvar2) {
                        if let Some(diff_vars) = diff_vars {
                            // diff_vars ∨ ¬tv1 ∨ tv2 (args same → tv1 implies tv2)
                            let mut c1 = diff_vars.clone();
                            c1.push(-(tv1 as i32));
                            c1.push(tv2 as i32);
                            all_clauses.push(z4_core::CnfClause::new(c1));
                            // diff_vars ∨ tv1 ∨ ¬tv2 (args same → tv2 implies tv1)
                            let mut c2 = diff_vars.clone();
                            c2.push(tv1 as i32);
                            c2.push(-(tv2 as i32));
                            all_clauses.push(z4_core::CnfClause::new(c2));
                        } else {
                            // All args identical — Tseitin vars must be equivalent
                            all_clauses
                                .push(z4_core::CnfClause::new(vec![-(tv1 as i32), tv2 as i32]));
                            all_clauses
                                .push(z4_core::CnfClause::new(vec![tv1 as i32, -(tv2 as i32)]));
                        }
                    }

                    // Distinct atom congruence (#5451): if (distinct f(a) f(b)) has a
                    // Tseitin variable, add congruence axioms for it too. Tseitin gives
                    // `distinct` its own standalone variable with NO built-in relationship
                    // to the `=` variable, so we must explicitly constrain it.
                    let dist_term = self.ctx.terms.mk_distinct(vec![*term1, *term2]);
                    if let Some(dist_tvar) = tseitin_result.var_for_term(dist_term) {
                        let dist_lit = dist_tvar as i32;
                        if let Some(dv) = diff_vars {
                            // Congruence: (args_differ) OR NOT(distinct f(a) f(b))
                            let mut clause = dv.clone();
                            clause.push(-dist_lit);
                            all_clauses.push(z4_core::CnfClause::new(clause));
                        } else {
                            // All args identical — distinct must be false
                            all_clauses.push(z4_core::CnfClause::unit(-dist_lit));
                        }
                    }
                }
            }
        }

        next_var.saturating_sub(var_offset + 1)
    }

    /// Build argument-difference SAT variables for a pair of UF applications.
    ///
    /// For each argument pair `(a_i, b_i)` that has BV bits, allocates a fresh
    /// `diff_i` variable encoding `a_i ≠ b_i` (XOR of corresponding bits).
    /// For non-BV argument pairs, looks up the Tseitin variable for `(= a_i b_i)`
    /// and encodes `diff_i ↔ ¬eq_var` (#5439).
    ///
    /// Returns:
    /// - `ArgDiffResult::AllIdentical` — all argument pairs are the same TermId
    /// - `ArgDiffResult::Encoded(diff_vars)` — all different pairs encodable
    /// - `ArgDiffResult::Unencodable` — some pairs differ but lack encoding (#5457)
    #[allow(clippy::too_many_arguments)]
    fn build_arg_diff_vars(
        terms: &mut z4_core::TermStore,
        args1: &[TermId],
        args2: &[TermId],
        term_bits: &HashMap<TermId, Vec<i32>>,
        tseitin_result: &z4_core::TseitinResult,
        bv_offset: u32,
        _arg_eq_lits: &[Option<i32>],
        next_var: &mut u32,
        clauses: &mut Vec<z4_core::CnfClause>,
    ) -> ArgDiffResult {
        let offset_bit = |bit: i32| -> i32 {
            if bit > 0 {
                bit + bv_offset as i32
            } else {
                bit - bv_offset as i32
            }
        };

        let mut all_diff_vars = Vec::new();
        let mut has_unencodable_diff = false;

        for (arg1, arg2) in args1.iter().zip(args2.iter()) {
            if arg1 == arg2 {
                // Identical arguments — no difference possible
                continue;
            }
            let arg1_bits = term_bits.get(arg1).map(Vec::as_slice);
            let arg2_bits = term_bits.get(arg2).map(Vec::as_slice);

            match (arg1_bits, arg2_bits) {
                (Some(b1), Some(b2)) if b1.len() == b2.len() && !b1.is_empty() => {
                    for (&bit1, &bit2) in b1.iter().zip(b2.iter()) {
                        let ob1 = offset_bit(bit1);
                        let ob2 = offset_bit(bit2);
                        let diff_var = *next_var as i32;
                        *next_var += 1;
                        all_diff_vars.push(diff_var);

                        // diff_var ↔ (bit1 XOR bit2)
                        clauses.push(z4_core::CnfClause::new(vec![-diff_var, ob1, ob2]));
                        clauses.push(z4_core::CnfClause::new(vec![-diff_var, -ob1, -ob2]));
                        clauses.push(z4_core::CnfClause::new(vec![-ob1, ob2, diff_var]));
                        clauses.push(z4_core::CnfClause::new(vec![ob1, -ob2, diff_var]));
                    }
                }
                _ => {
                    // Non-BV argument pair: try Tseitin-variable encoding (#5439).
                    // Look up (= arg1 arg2) in Tseitin result; if present, encode
                    // diff_i ↔ ¬eq_var (arguments differ ↔ equality is false).
                    // Sort mismatch means args can never be equal (#2682).
                    if terms.sort(*arg1) != terms.sort(*arg2) {
                        has_unencodable_diff = true;
                        continue;
                    }
                    let eq_term = terms.mk_eq(*arg1, *arg2);
                    if let Some(eq_tvar) = tseitin_result.var_for_term(eq_term) {
                        let eq_lit = eq_tvar as i32;
                        let diff_var = *next_var as i32;
                        *next_var += 1;
                        all_diff_vars.push(diff_var);
                        // diff_var ↔ ¬eq_lit
                        clauses.push(z4_core::CnfClause::new(vec![-diff_var, -eq_lit]));
                        clauses.push(z4_core::CnfClause::new(vec![eq_lit, diff_var]));
                    } else {
                        // No BV bits and no Tseitin variable — unencodable (#5457).
                        has_unencodable_diff = true;
                    }
                    continue;
                }
            }
        }

        if has_unencodable_diff {
            ArgDiffResult::Unencodable
        } else if all_diff_vars.is_empty() {
            ArgDiffResult::AllIdentical
        } else {
            ArgDiffResult::Encoded(all_diff_vars)
        }
    }
}

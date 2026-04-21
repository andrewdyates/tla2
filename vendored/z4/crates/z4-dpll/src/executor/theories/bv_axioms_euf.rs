// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV-return EUF congruence axiom generation for combined BV theories (UFBV, AUFBV).
//!
//! Generates congruence axioms for uninterpreted functions with BV return types
//! as CNF clauses using bit-level XOR diff vars. Also contains the shared
//! `collect_uf_applications` traversal used by both this module and sibling
//! `bv_axioms_non_bv.rs` (non-BV return type congruence).
//!
//! Split from `bv_axioms.rs` for code health (#7006, #5970).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use z4_bv::BvSolver;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Symbol, TermData};
use z4_core::TermId;

use super::super::Executor;
use super::EufAxiomResult;

impl Executor {
    /// Ensure UF application arguments that are BV-sorted are bitblasted before
    /// congruence axiom generation. Complex BV sub-expressions (e.g., `bvadd(x, #x01)`)
    /// inside UF calls are opaque to the BV bitblaster and need explicit materialization,
    /// just like array indices need materialization in `materialize_array_bv_terms`.
    /// Without this, `get_term_bits` returns None for complex BV args, causing the
    /// congruence axiom to be skipped entirely (#5475 Gap B).
    pub(in crate::executor) fn materialize_uf_arg_bv_terms(
        &self,
        bv_solver: &mut BvSolver<'_>,
        extra_terms: &[TermId],
    ) {
        let mut uf_apps: HashMap<String, Vec<(TermId, Vec<TermId>)>> = HashMap::new();
        let mut visited = HashSet::new();
        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        for (_name, applications) in &uf_apps {
            for (_term, args) in applications {
                for &arg in args {
                    let _ = bv_solver.ensure_term_bits(arg);
                }
            }
            // Also ensure result term bits are available
            for (term, _args) in applications {
                let _ = bv_solver.ensure_term_bits(*term);
            }
        }
    }

    /// Generate EUF congruence axiom clauses for QF_UFBV/QF_AUFBV (with debug output)
    pub(in crate::executor) fn generate_euf_bv_axioms_debug(
        &self,
        bv_solver: &BvSolver<'_>,
        bv_offset: u32,
        var_offset: u32,
        debug: bool,
        extra_terms: &[TermId],
    ) -> EufAxiomResult {
        let mut result = EufAxiomResult {
            clauses: Vec::new(),
            num_vars: 0,
        };

        // Collect all uninterpreted function applications from assertions AND
        // extra terms (e.g., assumptions). UF applications in assumptions like
        // `distinct(f(x), f(y))` must be included for congruence axiom generation.
        let mut uf_apps: HashMap<String, Vec<(TermId, Vec<TermId>)>> = HashMap::new();
        let mut visited = HashSet::new();

        for &assertion in &self.ctx.assertions {
            self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
        }
        for &term in extra_terms {
            self.collect_uf_applications(term, &mut uf_apps, &mut visited);
        }

        if debug {
            safe_eprintln!("DEBUG: Collected UF applications:");
            for (name, apps) in &uf_apps {
                safe_eprintln!("  Function '{}' has {} applications:", name, apps.len());
                for (term, args) in apps {
                    let term_bits = bv_solver.get_term_bits(*term);
                    safe_eprintln!(
                        "    Term {:?} with args {:?}, bits: {:?}",
                        term,
                        args,
                        term_bits.map(<[i32]>::to_vec)
                    );
                    for (i, arg) in args.iter().enumerate() {
                        let arg_bits = bv_solver.get_term_bits(*arg);
                        safe_eprintln!(
                            "      Arg {}: term {:?}, bits: {:?}",
                            i,
                            arg,
                            arg_bits.map(<[i32]>::to_vec)
                        );
                    }
                }
            }
        }

        let mut next_var = var_offset + 1;

        for (func_name, applications) in &uf_apps {
            if applications.len() < 2 {
                continue;
            }

            // All applications of the same UF must have the same arity (#4661)
            debug_assert!(
                applications
                    .windows(2)
                    .all(|w| w[0].1.len() == w[1].1.len()),
                "BUG: UF '{func_name}' has applications with inconsistent arities"
            );

            for i in 0..applications.len() {
                for j in (i + 1)..applications.len() {
                    let (term1, args1) = &applications[i];
                    let (term2, args2) = &applications[j];

                    if args1.len() != args2.len() {
                        continue;
                    }

                    let bits1 = match bv_solver.get_term_bits(*term1) {
                        Some(b) => b,
                        None => {
                            if debug {
                                safe_eprintln!(
                                    "DEBUG: Skipping pair - term1 {:?} has no bits",
                                    term1
                                );
                            }
                            continue;
                        }
                    };
                    let bits2 = match bv_solver.get_term_bits(*term2) {
                        Some(b) => b,
                        None => {
                            if debug {
                                safe_eprintln!(
                                    "DEBUG: Skipping pair - term2 {:?} has no bits",
                                    term2
                                );
                            }
                            continue;
                        }
                    };

                    if bits1.len() != bits2.len() || bits1.is_empty() {
                        continue;
                    }

                    if debug {
                        safe_eprintln!(
                            "DEBUG: Generating congruence axiom for {}({:?}) and {}({:?})",
                            func_name,
                            args1,
                            func_name,
                            args2
                        );
                        safe_eprintln!("  term1 bits (unoffset): {:?}", bits1);
                        safe_eprintln!("  term2 bits (unoffset): {:?}", bits2);
                    }

                    let offset_bit = |bit: i32| -> i32 {
                        if bit > 0 {
                            bit + bv_offset as i32
                        } else {
                            bit - bv_offset as i32
                        }
                    };

                    let mut all_diff_vars = Vec::new();
                    let mut all_args_have_bits = true;

                    for (arg_idx, (arg1, arg2)) in args1.iter().zip(args2.iter()).enumerate() {
                        // Identical arguments cannot differ — skip (#5457).
                        // Without this, get_term_bits on a shared arg that was
                        // never independently bitblasted returns None, which
                        // sets all_args_have_bits=false and drops the entire
                        // congruence axiom for the pair.
                        if arg1 == arg2 {
                            continue;
                        }
                        let arg1_bits = bv_solver.get_term_bits(*arg1);
                        let arg2_bits = bv_solver.get_term_bits(*arg2);

                        match (arg1_bits, arg2_bits) {
                            (Some(b1), Some(b2)) if b1.len() == b2.len() && !b1.is_empty() => {
                                if debug {
                                    safe_eprintln!(
                                        "  Arg {} pair: {:?} vs {:?}",
                                        arg_idx,
                                        arg1,
                                        arg2
                                    );
                                    safe_eprintln!("    arg1 bits (unoffset): {:?}", b1);
                                    safe_eprintln!("    arg2 bits (unoffset): {:?}", b2);
                                }

                                for (bit_idx, (&bit1, &bit2)) in
                                    b1.iter().zip(b2.iter()).enumerate()
                                {
                                    let ob1 = offset_bit(bit1);
                                    let ob2 = offset_bit(bit2);
                                    let diff_var = next_var as i32;
                                    next_var += 1;
                                    all_diff_vars.push(diff_var);

                                    if debug && bit_idx < 2 {
                                        safe_eprintln!(
                                            "    bit {}: diff_var={}, ob1={}, ob2={}",
                                            bit_idx,
                                            diff_var,
                                            ob1,
                                            ob2
                                        );
                                    }

                                    // diff_j ↔ (b1[j] XOR b2[j])
                                    result
                                        .clauses
                                        .push(z4_core::CnfClause::new(vec![-diff_var, ob1, ob2]));
                                    result
                                        .clauses
                                        .push(z4_core::CnfClause::new(vec![-diff_var, -ob1, -ob2]));
                                    result
                                        .clauses
                                        .push(z4_core::CnfClause::new(vec![-ob1, ob2, diff_var]));
                                    result
                                        .clauses
                                        .push(z4_core::CnfClause::new(vec![ob1, -ob2, diff_var]));
                                }
                            }
                            _ => {
                                if debug {
                                    safe_eprintln!(
                                        "  Arg {} pair: {:?} vs {:?} - MISSING BITS",
                                        arg_idx,
                                        arg1,
                                        arg2
                                    );
                                    safe_eprintln!(
                                        "    arg1_bits: {:?}",
                                        arg1_bits.map(<[i32]>::to_vec)
                                    );
                                    safe_eprintln!(
                                        "    arg2_bits: {:?}",
                                        arg2_bits.map(<[i32]>::to_vec)
                                    );
                                }
                                all_args_have_bits = false;
                                break;
                            }
                        }
                    }

                    if !all_args_have_bits || all_diff_vars.is_empty() {
                        if debug {
                            safe_eprintln!(
                                "  SKIPPING - all_args_have_bits={}, diff_vars={}",
                                all_args_have_bits,
                                all_diff_vars.len()
                            );
                        }
                        continue;
                    }

                    if debug {
                        safe_eprintln!("  Generated {} diff vars", all_diff_vars.len());
                    }

                    // For each result bit, add the congruence constraint:
                    // diff_0 ∨ diff_1 ∨ ... ∨ ¬f(a)[i] ∨ f(b)[i]
                    // diff_0 ∨ diff_1 ∨ ... ∨ f(a)[i] ∨ ¬f(b)[i]
                    // These two clauses encode: (args differ) ∨ (f(a)[i] = f(b)[i])
                    //
                    // Optimization: Pre-allocate clause buffer to avoid O(n²) cloning.
                    // The shared prefix (diff vars) is copied once; suffix is modified in-place.
                    let suffix_start = all_diff_vars.len();
                    let mut clause_buf = Vec::with_capacity(suffix_start + 2);
                    clause_buf.extend_from_slice(&all_diff_vars);
                    clause_buf.push(0); // Placeholder for bit1 literal
                    clause_buf.push(0); // Placeholder for bit2 literal

                    for (&bit1, &bit2) in bits1.iter().zip(bits2.iter()) {
                        let ob1 = offset_bit(bit1);
                        let ob2 = offset_bit(bit2);

                        // Clause 1: diff_0 ∨ ... ∨ ¬f(a)[i] ∨ f(b)[i]
                        clause_buf[suffix_start] = -ob1;
                        clause_buf[suffix_start + 1] = ob2;
                        result
                            .clauses
                            .push(z4_core::CnfClause::new(clause_buf.clone()));

                        // Clause 2: diff_0 ∨ ... ∨ f(a)[i] ∨ ¬f(b)[i]
                        clause_buf[suffix_start] = ob1;
                        clause_buf[suffix_start + 1] = -ob2;
                        result
                            .clauses
                            .push(z4_core::CnfClause::new(clause_buf.clone()));
                    }
                }
            }
        }

        result.num_vars = next_var.saturating_sub(var_offset + 1);
        result
    }

    /// Recursively collect uninterpreted function applications from an expression
    pub(in crate::executor) fn collect_uf_applications(
        &self,
        term: TermId,
        uf_apps: &mut HashMap<String, Vec<(TermId, Vec<TermId>)>>,
        visited: &mut HashSet<TermId>,
    ) {
        if visited.contains(&term) {
            return;
        }
        visited.insert(term);

        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                // Check if this is an uninterpreted function (not a built-in BV or array op)
                let is_builtin = matches!(
                    name.as_str(),
                    "bvadd"
                        | "bvsub"
                        | "bvmul"
                        | "bvudiv"
                        | "bvurem"
                        | "bvsdiv"
                        | "bvsrem"
                        | "bvand"
                        | "bvor"
                        | "bvxor"
                        | "bvnot"
                        | "bvneg"
                        | "bvshl"
                        | "bvlshr"
                        | "bvashr"
                        | "concat"
                        | "extract"
                        | "repeat"
                        | "zero_extend"
                        | "sign_extend"
                        | "rotate_left"
                        | "rotate_right"
                        | "bvult"
                        | "bvule"
                        | "bvugt"
                        | "bvuge"
                        | "bvslt"
                        | "bvsle"
                        | "bvsgt"
                        | "bvsge"
                        | "="
                        | "distinct"
                        | "ite"
                        | "and"
                        | "or"
                        | "not"
                        | "=>"
                        | "xor"
                        | "select"
                        | "store"
                        | "true"
                        | "false"
                );

                if !is_builtin && !args.is_empty() {
                    // This is an uninterpreted function application
                    uf_apps
                        .entry(name.clone())
                        .or_default()
                        .push((term, args.clone()));
                }

                // Recurse into arguments
                for &arg in args {
                    self.collect_uf_applications(arg, uf_apps, visited);
                }
            }
            TermData::App(Symbol::Indexed(name, _), args) => {
                // Indexed symbols like (_ extract ...) are built-in
                // Just recurse into arguments
                for &arg in args {
                    self.collect_uf_applications(arg, uf_apps, visited);
                }

                // But user-defined indexed functions should be tracked
                let is_builtin = matches!(
                    name.as_str(),
                    "extract"
                        | "repeat"
                        | "zero_extend"
                        | "sign_extend"
                        | "rotate_left"
                        | "rotate_right"
                );

                if !is_builtin && !args.is_empty() {
                    uf_apps
                        .entry(name.clone())
                        .or_default()
                        .push((term, args.clone()));
                }
            }
            TermData::Not(inner) => {
                self.collect_uf_applications(*inner, uf_apps, visited);
            }
            TermData::Ite(c, t, e) => {
                self.collect_uf_applications(*c, uf_apps, visited);
                self.collect_uf_applications(*t, uf_apps, visited);
                self.collect_uf_applications(*e, uf_apps, visited);
            }
            _ => {}
        }
    }
}

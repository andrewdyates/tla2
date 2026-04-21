// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! E-Matching module for quantifier instantiation.
//!
//! Implements pattern-based E-matching to instantiate universal quantifiers
//! by matching patterns against ground terms in the term store.
//!
//! Author: Andrew Yates

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::TermData;
use z4_core::{TermId, TermStore};
use z4_euf::EufModel;

/// Red zone size for `stacker::maybe_grow` in ematching recursion (#5612).
const EMATCH_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for ematching recursion.
const EMATCH_STACK_SIZE: usize = 1024 * 1024;

/// Maximum number of binding combinations in multi-trigger cross-product join.
/// Prevents combinatorial explosion when many candidate matches exist per trigger term.
const MAX_MULTI_TRIGGER_BINDINGS: usize = 1000;

/// Check if a term contains any quantifiers (forall or exists).
/// Used to return `unknown` for formulas with quantifiers that we can't fully handle.
///
/// Uses a visited set to avoid exponential re-traversal on DAG-structured terms.
/// Without memoization, deeply nested formulas (e.g., countbitstableoffbyone0128
/// with 128-bit BV + 256 stores) cause exponential blowup because shared
/// sub-terms are visited once per parent path.
pub(crate) fn contains_quantifier(terms: &TermStore, term: TermId) -> bool {
    let mut visited = HashSet::new();
    contains_quantifier_memo(terms, term, &mut visited)
}

fn contains_quantifier_memo(
    terms: &TermStore,
    term: TermId,
    visited: &mut HashSet<TermId>,
) -> bool {
    if !visited.insert(term) {
        return false;
    }
    stacker::maybe_grow(EMATCH_STACK_RED_ZONE, EMATCH_STACK_SIZE, || {
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) => true,
            TermData::Not(inner) => contains_quantifier_memo(terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                contains_quantifier_memo(terms, *c, visited)
                    || contains_quantifier_memo(terms, *t, visited)
                    || contains_quantifier_memo(terms, *e, visited)
            }
            TermData::App(_, args) => args
                .iter()
                .any(|&arg| contains_quantifier_memo(terms, arg, visited)),
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, val)| contains_quantifier_memo(terms, *val, visited))
                    || contains_quantifier_memo(terms, *body, visited)
            }
            TermData::Const(_) | TermData::Var(_, _) => false,
            // Future TermData variants: conservatively assume no quantifiers.
            _ => false,
        }
    })
}

mod ground_terms;
mod matching;
mod pattern;
mod pattern_helpers;
mod substitution;
pub(crate) use ground_terms::{collect_ground_terms_by_sort, enumerative_instantiation};
use matching::{match_multi_trigger, match_pattern};
use pattern::{extract_patterns, EqualityClasses, TermIndex};
#[cfg(test)]
use pattern_helpers::pattern_covered_vars;
#[cfg(test)]
use substitution::collect_free_var_names;
use substitution::instantiate_body;
pub(crate) use substitution::subst_vars;

/// Configuration for E-matching instantiation limits.
///
/// These limits prevent infinite loops from self-triggering patterns like:
/// `(forall ((x Int)) (P (f x)))` with `(P (f (f (f a))))`.
///
/// Generation tracking provides cost-based filtering:
/// - Input problem terms have generation 0
/// - Terms from instantiation round N get generation = max(binding_generations) + 1
/// - Instantiation cost = weight + generation
/// - High-cost instantiations are deferred or blocked
///
/// Reference: Z3 smt/smt_enode.h:67, sat/smt/q_ematch.cpp:425-430
#[derive(Clone, Debug)]
pub(crate) struct EMatchingConfig {
    pub(crate) max_per_quantifier: usize,
    pub(crate) max_total: usize,
    pub(crate) eager_threshold: f64,
    pub(crate) lazy_threshold: f64,
    pub(crate) default_weight: f64,
}

impl Default for EMatchingConfig {
    fn default() -> Self {
        Self {
            max_per_quantifier: 1000,
            max_total: 10000,
            eager_threshold: 10.0,
            lazy_threshold: 20.0,
            default_weight: 1.0,
        }
    }
}

/// Tracks generation (age) of terms for cost-based instantiation filtering.
///
/// Generation tracking prevents infinite instantiation loops more intelligently
/// than count limits by assigning a cost to each potential instantiation based
/// on how "deep" the matched terms are in the instantiation chain.
///
/// - Generation 0: Input problem terms
/// - Generation N: Terms created from instantiations where max binding generation was N-1
///
/// Reference: Z3 smt/smt_enode.h:67, qi_queue.cpp:127-134
#[derive(Clone, Debug, Default)]
pub(crate) struct GenerationTracker {
    /// Generation per term. Terms not in this map have generation 0.
    generations: HashMap<u32, u32>,
    /// Current round number (incremented each E-matching pass).
    current_round: u32,
}

impl GenerationTracker {
    /// Create a new generation tracker.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Get the generation of a term (0 if not tracked).
    pub(crate) fn get(&self, term: TermId) -> u32 {
        *self.generations.get(&term.0).unwrap_or(&0)
    }

    /// Set the generation of a term.
    pub(crate) fn set(&mut self, term: TermId, generation: u32) {
        // Don't store generation 0 to save memory
        if generation > 0 {
            self.generations.insert(term.0, generation);
        }
    }

    /// Get the maximum generation among a set of terms.
    pub(crate) fn max_generation(&self, terms: &[TermId]) -> u32 {
        terms.iter().map(|t| self.get(*t)).max().unwrap_or(0)
    }

    /// Compute instantiation cost: weight + max_binding_generation.
    pub(crate) fn instantiation_cost(&self, binding: &[TermId], weight: f64) -> f64 {
        weight + f64::from(self.max_generation(binding))
    }

    /// Start a new round of E-matching.
    pub(crate) fn next_round(&mut self) {
        self.current_round += 1;
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
impl GenerationTracker {
    pub(crate) fn current_round(&self) -> u32 {
        self.current_round
    }
}

/// Result of E-matching: instantiations plus soundness info.
pub(crate) struct EMatchingResult {
    /// Ground instantiations derived from quantified formulas.
    pub instantiations: Vec<TermId>,
    /// True if any quantifier had no matching ground terms.
    /// When true and solver returns Sat, we must return Unknown instead.
    pub has_uninstantiated: bool,
    /// Set of quantifier term IDs that had no ground matches.
    /// Used by CEGQI to only add counterexample lemmas for uninstantiated quantifiers (#1939).
    pub uninstantiated_quantifiers: HashSet<TermId>,
    /// True if instantiation limit was reached.
    /// When true, result is incomplete and solver should return Unknown.
    pub reached_limit: bool,
    /// Deferred instantiations (cost > eager_threshold but <= lazy_threshold).
    pub deferred: Vec<DeferredInstantiation>,
    /// Updated generation tracker with new term generations.
    pub generation_tracker: GenerationTracker,
}

/// A deferred instantiation for later processing.
#[derive(Clone, Debug)]
pub(crate) struct DeferredInstantiation {
    /// The quantifier being instantiated.
    pub quantifier: TermId,
    /// The variable bindings (term IDs for each bound variable).
    pub binding: Vec<TermId>,
    /// The actual variable names in the quantifier body (needed for instantiation).
    pub var_names: Vec<String>,
}

impl DeferredInstantiation {
    /// Instantiate this deferred entry, producing the actual term.
    ///
    /// This is used for promote-unsat (Phase D): we need the actual term
    /// to check if it would create a conflict under the current model.
    pub(crate) fn instantiate(&self, terms: &mut TermStore) -> Option<TermId> {
        // Get the body of the quantifier
        let body = match terms.get(self.quantifier) {
            TermData::Forall(_, b, _) => *b,
            TermData::Exists(_, b, _) => *b,
            _ => return None,
        };

        // Substitute the bindings into the body
        Some(instantiate_body(
            terms,
            body,
            &self.var_names,
            &self.binding,
        ))
    }
}

/// Perform E-matching with generation tracking for cost-based filtering.
///
/// Generation tracking assigns a "depth" to each term:
/// - Input terms have generation 0
/// - Terms created from instantiation get generation = max(binding_generations) + 1
///
/// Instantiation cost = weight + max_binding_generation.
/// - cost <= eager_threshold: instantiate immediately
/// - eager_threshold < cost <= lazy_threshold: defer for later
/// - cost > lazy_threshold: skip (blocked)
pub(crate) fn perform_ematching_with_generations(
    terms: &mut TermStore,
    assertions: &[TermId],
    config: &EMatchingConfig,
    mut tracker: GenerationTracker,
    euf_model: Option<&EufModel>,
) -> EMatchingResult {
    let mut quantifiers = Vec::new();
    for &assertion in assertions {
        collect_quantifiers(terms, assertion, &mut quantifiers);
    }

    if quantifiers.is_empty() {
        return EMatchingResult {
            instantiations: vec![],
            has_uninstantiated: false,
            uninstantiated_quantifiers: HashSet::new(),
            reached_limit: false,
            deferred: vec![],
            generation_tracker: tracker,
        };
    }

    tracker.next_round();

    let index = TermIndex::new(terms, assertions);
    // Build equality classes from explicit equalities in assertions (#3325 Gap 1).
    // This allows E-matching to match modulo known equalities (e.g., g(a) = c).
    let mut eqclasses = EqualityClasses::from_assertions(terms, assertions);
    // Phase B1b (#3325): augment with congruence classes from EUF model.
    // Terms with the same model value are congruent, enabling deeper matching.
    if let Some(model) = euf_model {
        eqclasses.augment_with_euf_model(model);
    }
    let eqclasses_opt = if eqclasses.is_empty() {
        None
    } else {
        Some(&eqclasses)
    };
    let mut instantiations = Vec::new();
    let mut deferred = Vec::new();
    let mut seen: HashSet<(TermId, Vec<TermId>)> = HashSet::new();
    let mut instantiated_quantifiers: HashSet<TermId> = HashSet::new();
    let mut per_quantifier_count: HashMap<TermId, usize> = HashMap::new();
    let mut reached_limit = false;

    'outer: for &quant in &quantifiers {
        let patterns = extract_patterns(terms, quant);
        let body = match terms.get(quant) {
            TermData::Forall(_, b, _) => *b,
            TermData::Exists(_, b, _) => *b,
            _ => continue,
        };

        let quant_count = per_quantifier_count.entry(quant).or_insert(0);

        for trigger_group in &patterns {
            let vars = &trigger_group.var_names;

            // Collect all bindings for this trigger group.
            // Single trigger: fast path using direct candidate lookup.
            // Multi-trigger: join across all patterns with consistent bindings.
            let bindings: Vec<Vec<TermId>> = if trigger_group.patterns.len() == 1 {
                let pattern = &trigger_group.patterns[0];
                let candidates = index.get_by_symbol(pattern.symbol.name());
                candidates
                    .iter()
                    .filter_map(|&gt| match_pattern(terms, pattern, gt, vars.len(), eqclasses_opt))
                    .collect()
            } else {
                match_multi_trigger(
                    terms,
                    &trigger_group.patterns,
                    &index,
                    vars.len(),
                    eqclasses_opt,
                )
            };

            for binding in bindings {
                if instantiations.len() >= config.max_total {
                    reached_limit = true;
                    break 'outer;
                }

                if *quant_count >= config.max_per_quantifier {
                    reached_limit = true;
                    break;
                }

                let key = (quant, binding.clone());
                if seen.contains(&key) {
                    continue;
                }
                seen.insert(key);

                // Compute instantiation cost based on generation
                let cost = tracker.instantiation_cost(&binding, config.default_weight);

                if cost > config.lazy_threshold {
                    continue; // Cost too high - skip
                }

                if cost > config.eager_threshold {
                    // Deferred still counts as "instantiated" for soundness
                    instantiated_quantifiers.insert(quant);
                    deferred.push(DeferredInstantiation {
                        quantifier: quant,
                        binding: binding.clone(),
                        var_names: vars.clone(),
                    });
                    continue;
                }

                instantiated_quantifiers.insert(quant);
                let inst = instantiate_body(terms, body, vars, &binding);

                // Set generation: max(binding_generations) + 1, minimum 1
                let max_binding_gen = tracker.max_generation(&binding);
                let new_gen = max_binding_gen.saturating_add(1).max(1);
                tracker.set(inst, new_gen);
                set_subterm_generations(terms, inst, new_gen, &mut tracker);

                instantiations.push(inst);
                *quant_count += 1;
            }
        }
    }

    // Compute which quantifiers had no ground matches (#1939)
    let uninstantiated_quantifiers: HashSet<TermId> = quantifiers
        .iter()
        .copied()
        .filter(|q| !instantiated_quantifiers.contains(q))
        .collect();
    let has_uninstantiated = !uninstantiated_quantifiers.is_empty();

    EMatchingResult {
        instantiations,
        has_uninstantiated,
        uninstantiated_quantifiers,
        reached_limit,
        deferred,
        generation_tracker: tracker,
    }
}

/// Set generation for all subterms of a term (if they don't already have one).
///
/// Early-returns if the term already has a non-zero generation to avoid redundant work
/// and prevent setting generation on pre-existing input terms.
fn set_subterm_generations(
    terms: &TermStore,
    term: TermId,
    generation: u32,
    tracker: &mut GenerationTracker,
) {
    // Skip if term already has a generation (either from input or previous instantiation)
    if tracker.get(term) != 0 {
        return;
    }
    tracker.set(term, generation);

    match terms.get(term) {
        TermData::App(_, args) => {
            for &arg in args {
                set_subterm_generations(terms, arg, generation, tracker);
            }
        }
        TermData::Not(inner) => set_subterm_generations(terms, *inner, generation, tracker),
        TermData::Ite(c, t, e) => {
            set_subterm_generations(terms, *c, generation, tracker);
            set_subterm_generations(terms, *t, generation, tracker);
            set_subterm_generations(terms, *e, generation, tracker);
        }
        TermData::Let(bindings, body) => {
            for (_, v) in bindings {
                set_subterm_generations(terms, *v, generation, tracker);
            }
            set_subterm_generations(terms, *body, generation, tracker);
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            set_subterm_generations(terms, *body, generation, tracker);
        }
        TermData::Const(_) | TermData::Var(_, _) => {}
        // Future TermData variants: skip (no subterms to set).
        _ => {}
    }
}

/// Collect all quantified formulas from a term.
///
/// Applies NNF (Negation Normal Form) conversion for negated quantifiers:
///   NOT(exists x. phi) → forall x. NOT(phi)
///   NOT(forall x. phi) → exists x. NOT(phi)
/// This is critical for soundness: without it, E-matching instantiates the body
/// with wrong polarity, producing false UNSAT results (#3593).
fn collect_quantifiers(terms: &mut TermStore, term: TermId, out: &mut Vec<TermId>) {
    match terms.get(term).clone() {
        TermData::Forall(..) | TermData::Exists(..) => {
            out.push(term);
        }
        TermData::Not(inner) => {
            match terms.get(inner).clone() {
                // NNF: NOT(exists x. phi) → forall x. NOT(phi)
                TermData::Exists(vars, body, triggers) => {
                    let neg_body = terms.mk_not(body);
                    let converted = terms.mk_forall_with_triggers(vars, neg_body, triggers);
                    out.push(converted);
                }
                // NNF: NOT(forall x. phi) → exists x. NOT(phi)
                TermData::Forall(vars, body, triggers) => {
                    let neg_body = terms.mk_not(body);
                    let converted = terms.mk_exists_with_triggers(vars, neg_body, triggers);
                    out.push(converted);
                }
                _ => collect_quantifiers(terms, inner, out),
            }
        }
        TermData::App(_, args) => {
            for arg in args {
                collect_quantifiers(terms, arg, out);
            }
        }
        TermData::Ite(c, t, e) => {
            collect_quantifiers(terms, c, out);
            collect_quantifiers(terms, t, out);
            collect_quantifiers(terms, e, out);
        }
        TermData::Let(bindings, body) => {
            let vals: Vec<TermId> = bindings.iter().map(|(_, v)| *v).collect();
            for val in vals {
                collect_quantifiers(terms, val, out);
            }
            collect_quantifiers(terms, body, out);
        }
        TermData::Const(_) | TermData::Var(_, _) => {}
        // Future TermData variants: skip (no quantifiers to collect).
        _ => {}
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
fn perform_ematching(terms: &mut TermStore, assertions: &[TermId]) -> EMatchingResult {
    perform_ematching_with_generations(
        terms,
        assertions,
        &EMatchingConfig::default(),
        GenerationTracker::new(),
        None,
    )
}

#[allow(clippy::panic)]
#[cfg(test)]
fn perform_ematching_with_config(
    terms: &mut TermStore,
    assertions: &[TermId],
    config: &EMatchingConfig,
) -> EMatchingResult {
    perform_ematching_with_generations(terms, assertions, config, GenerationTracker::new(), None)
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

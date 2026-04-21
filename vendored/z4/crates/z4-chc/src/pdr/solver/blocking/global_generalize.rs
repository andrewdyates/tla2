// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) fn try_global_generalization(
        &mut self,
        blocking_formula: &ChcExpr,
        pob: &mut ProofObligation,
        is_on_counterexample_path: bool,
    ) -> ChcExpr {
        let mut final_blocking_formula = blocking_formula.clone();
        if self.config.use_convex_closure && !is_on_counterexample_path {
            if let Some(idx) = self.caches.cluster_store.add_blocking_cube(
                pob.predicate,
                blocking_formula,
                pob.level,
            ) {
                let extracted_state_values = if pob.smt_model.is_some() {
                    None
                } else {
                    Some(self.extract_point_values_from_state(&pob.state))
                };
                let state_values = match pob.smt_model.as_ref() {
                    Some(model) => model,
                    None => extracted_state_values
                        .as_ref()
                        .expect("extracted when smt_model is None"),
                };

                let (min_max_candidates, eligible_for_subsume) = self
                    .caches
                    .cluster_store
                    .get_clusters(pob.predicate)
                    .and_then(|cs| cs.get(idx))
                    .map_or((Vec::new(), false), |cluster| {
                        (
                            cluster.propose_min_max_blocking_cubes(),
                            cluster.is_eligible(),
                        )
                    });

                for candidate in min_max_candidates {
                    if !self.point_values_satisfy_cube(&candidate, state_values) {
                        continue;
                    }
                    if self.predicate_has_facts(pob.predicate)
                        && !self.blocks_initial_states(pob.predicate, &candidate)
                    {
                        continue;
                    }
                    if self.is_safety_path_point_blocking_acceptable(
                        &candidate,
                        pob.predicate,
                        pob.level,
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Cluster min/max generalized blocking cube: {} -> {}",
                                blocking_formula,
                                candidate
                            );
                        }
                        final_blocking_formula = candidate;
                        self.caches.cluster_store.add_blocking_cube(
                            pob.predicate,
                            &final_blocking_formula,
                            pob.level,
                        );
                        break;
                    }
                }

                if final_blocking_formula == *blocking_formula && eligible_for_subsume {
                    let cluster = self
                        .caches
                        .cluster_store
                        .get_clusters(pob.predicate)
                        .and_then(|cs| cs.get(idx))
                        .cloned();

                    if let Some(cluster) = cluster {
                        let generalized = self.try_cluster_subsume(&cluster, pob.level);
                        if let Some(clusters_mut) =
                            self.caches.cluster_store.get_clusters_mut(pob.predicate)
                        {
                            if let Some(cluster_mut) = clusters_mut.get_mut(idx) {
                                cluster_mut.dec_gas();
                            }
                        }

                        if let Some(generalized) = generalized {
                            if self.point_values_satisfy_cube(&generalized, state_values)
                                && (!self.predicate_has_facts(pob.predicate)
                                    || self.blocks_initial_states(pob.predicate, &generalized))
                                && self.is_safety_path_point_blocking_acceptable(
                                    &generalized,
                                    pob.predicate,
                                    pob.level,
                                )
                            {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Global generalizer produced: {} (was: {})",
                                        generalized,
                                        blocking_formula
                                    );
                                }
                                final_blocking_formula = generalized;
                                self.caches.cluster_store.add_blocking_cube(
                                    pob.predicate,
                                    &final_blocking_formula,
                                    pob.level,
                                );
                            }
                        }
                    }
                }

                if final_blocking_formula == *blocking_formula {
                    let conjecture_info = self
                        .caches
                        .cluster_store
                        .get_clusters(pob.predicate)
                        .and_then(|cs| cs.get(idx))
                        .and_then(|cluster| {
                            if !cluster.is_eligible() || cluster.gas == 0 {
                                return None;
                            }
                            let mono_var_lit = cluster.find_mono_var_literal()?;
                            let pattern_var = cluster.pattern_vars.first()?.clone();
                            Some((mono_var_lit, pattern_var))
                        });

                    if let Some((mono_var_lit, pattern_var)) = conjecture_info {
                        let mut pob_conjuncts = Vec::new();
                        pob.state.collect_conjuncts_into(&mut pob_conjuncts);

                        let conjecture_formula = filter_out_lit_with_eq_retry(
                            &pob_conjuncts,
                            &mono_var_lit,
                            &pattern_var,
                        )
                        .or_else(|| {
                            let mut lemma_conjuncts = Vec::new();
                            blocking_formula.collect_conjuncts_into(&mut lemma_conjuncts);
                            filter_out_lit(&lemma_conjuncts, &mono_var_lit, &pattern_var)
                        });

                        if let Some(clusters_mut) =
                            self.caches.cluster_store.get_clusters_mut(pob.predicate)
                        {
                            if let Some(cluster_mut) = clusters_mut.get_mut(idx) {
                                cluster_mut.dec_gas();
                            }
                        }

                        if let Some(remaining) = conjecture_formula {
                            if !remaining.is_empty() {
                                let conj_formula = ChcExpr::and_all(remaining);
                                if self.point_values_satisfy_cube(&conj_formula, state_values)
                                    && (!self.predicate_has_facts(pob.predicate)
                                        || self.blocks_initial_states(pob.predicate, &conj_formula))
                                    && self.is_safety_path_point_blocking_acceptable(
                                        &conj_formula,
                                        pob.predicate,
                                        pob.level,
                                    )
                                {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Conjecture generalized blocking cube: {} -> {}",
                                            blocking_formula,
                                            conj_formula
                                        );
                                    }
                                    final_blocking_formula = conj_formula;
                                    self.caches.cluster_store.add_blocking_cube(
                                        pob.predicate,
                                        &final_blocking_formula,
                                        pob.level,
                                    );
                                } else if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Conjecture {} failed inductiveness/init check",
                                        conj_formula
                                    );
                                }
                            } else if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Conjecture empty after filtering mono-var from {}",
                                    blocking_formula
                                );
                            }
                        } else if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Conjecture filtering failed for mono-var lit {} in {}",
                                mono_var_lit,
                                blocking_formula
                            );
                        }
                    }
                }

                if final_blocking_formula == *blocking_formula {
                    let cluster_for_concretize = self
                        .caches
                        .cluster_store
                        .get_clusters(pob.predicate)
                        .and_then(|cs| cs.get(idx))
                        .map(|cluster| (cluster.pattern.clone(), cluster.pattern_vars.clone()));

                    if let Some((pattern, pattern_vars)) = cluster_for_concretize {
                        if crate::pdr::pob_concretize::has_nonlinear_pattern_vars(
                            &pattern,
                            &pattern_vars,
                        ) {
                            if let Some(model) = pob.smt_model.as_ref() {
                                let model_map: std::collections::HashMap<String, SmtValue> =
                                    model.iter().map(|(k, v)| (k.clone(), v.clone())).collect();

                                let mut pob_literals = Vec::new();
                                pob.state.collect_conjuncts_into(&mut pob_literals);

                                let mut concretizer =
                                    crate::pdr::pob_concretize::PobConcretizer::new(
                                        &pattern,
                                        &pattern_vars,
                                        &model_map,
                                    );

                                if let Some(concretized_lits) = concretizer.apply(&pob_literals) {
                                    if concretized_lits != pob_literals
                                        && !concretized_lits.is_empty()
                                    {
                                        let conc_formula = ChcExpr::and_all(concretized_lits);
                                        if self
                                            .point_values_satisfy_cube(&conc_formula, state_values)
                                            && (!self.predicate_has_facts(pob.predicate)
                                                || self.blocks_initial_states(
                                                    pob.predicate,
                                                    &conc_formula,
                                                ))
                                            && self.is_safety_path_point_blocking_acceptable(
                                                &conc_formula,
                                                pob.predicate,
                                                pob.level,
                                            )
                                        {
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: Concretization generalized blocking cube: {} -> {}",
                                                    blocking_formula,
                                                    conc_formula
                                                );
                                            }
                                            final_blocking_formula = conc_formula;
                                            self.caches.cluster_store.add_blocking_cube(
                                                pob.predicate,
                                                &final_blocking_formula,
                                                pob.level,
                                            );
                                        } else if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: Concretized formula {} failed validation",
                                                conc_formula
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        final_blocking_formula
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIC (Minimal Inductive Clause) generalization with CTG, domain restriction,
//! multi-ordering, activity management, and inductiveness checks.

use rustc_hash::FxHashMap;

use super::config::GeneralizationOrder;
use super::domain;
use super::engine::Ic3Engine;
use super::frame::Lemma;
use crate::sat_types::{Lit, SatResult, SatSolver, Var};

impl Ic3Engine {
    /// Bump activity for all variables in a cube.
    pub(super) fn bump_activity(&mut self, cube: &[Lit]) {
        self.vsids.bump_activity(cube);
    }

    /// Decay all activity scores.
    pub(super) fn decay_activity(&mut self) {
        self.vsids.decay_activity();
    }

    /// Sort MIC literals according to the configured generalization order.
    ///
    /// When `config.internal_signals` is true, applies a two-phase sort that
    /// partitions internal signal literals to the front of the array before
    /// applying the configured ordering within each group.
    ///
    /// This matches rIC3's `get_pred()` approach (solver.rs:74-78): when `--inn`
    /// is enabled, `cube.sort_by(|a, b| b.cmp(a))` puts high-index variables
    /// (internal signals) at the front. Since MIC's backward iteration
    /// (`while i > 0 { i -= 1; ... }`) tries to remove literals from the END
    /// first, literals at the FRONT are tried for removal LAST. This biases MIC
    /// toward keeping internal signals in the generalized clause, which produces
    /// shorter, more general lemmas on arithmetic circuits.
    pub(super) fn sort_for_generalization(&self, lits: &mut [Lit]) {
        if self.config.internal_signals && !self.ts.internal_signals.is_empty() {
            // Phase 1: Partition internal signals to front.
            // Internal signal variables have higher AIGER indices than latch
            // variables (AND-gate outputs are numbered after latches in AIGER).
            // We use a set lookup rather than relying on index ordering for
            // robustness.
            let isig_set: rustc_hash::FxHashSet<Var> =
                self.ts.internal_signals.iter().copied().collect();
            // Stable partition: internal signals first (!is_isig=false sorts
            // before !is_isig=true, putting isig=true literals at the front).
            lits.sort_by(|a, b| {
                let a_isig = isig_set.contains(&a.var());
                let b_isig = isig_set.contains(&b.var());
                (!a_isig).cmp(&(!b_isig))
            });
            // Phase 2: Apply configured ordering within each partition.
            let isig_count = lits.iter().filter(|l| isig_set.contains(&l.var())).count();
            let (isig_part, latch_part) = lits.split_at_mut(isig_count);
            self.sort_group(isig_part);
            self.sort_group(latch_part);
        } else {
            self.sort_group(lits);
        }
    }

    /// Sort a slice of MIC literals by the configured generalization order.
    fn sort_group(&self, lits: &mut [Lit]) {
        match self.config.gen_order {
            GeneralizationOrder::Activity => {
                self.vsids.sort_by_activity(lits);
            }
            GeneralizationOrder::ReverseTopological => {
                let depths = self.compute_and_gate_depths();
                lits.sort_by(|a, b| {
                    let da = depths.get(&a.var()).copied().unwrap_or(0);
                    let db = depths.get(&b.var()).copied().unwrap_or(0);
                    db.cmp(&da).then_with(|| a.var().cmp(&b.var()))
                });
            }
            GeneralizationOrder::RandomShuffle => {
                let seed = self.config.random_seed;
                lits.sort_by(|a, b| {
                    let ha = Self::hash_lit_with_seed(*a, seed);
                    let hb = Self::hash_lit_with_seed(*b, seed);
                    ha.cmp(&hb)
                });
            }
        }
    }

    /// Compute AND-gate depth for each variable in the transition system.
    pub(super) fn compute_and_gate_depths(&self) -> FxHashMap<Var, usize> {
        let mut depths: FxHashMap<Var, usize> = FxHashMap::default();

        fn depth_of(
            var: Var,
            and_defs: &FxHashMap<Var, (Lit, Lit)>,
            depths: &mut FxHashMap<Var, usize>,
        ) -> usize {
            if let Some(&d) = depths.get(&var) {
                return d;
            }
            let d = if let Some(&(rhs0, rhs1)) = and_defs.get(&var) {
                let d0 = depth_of(rhs0.var(), and_defs, depths);
                let d1 = depth_of(rhs1.var(), and_defs, depths);
                1 + d0.max(d1)
            } else {
                0
            };
            depths.insert(var, d);
            d
        }

        for &latch_var in &self.ts.latch_vars {
            depth_of(latch_var, &self.ts.and_defs, &mut depths);
            if let Some(&next_lit) = self.ts.next_state.get(&latch_var) {
                depth_of(next_lit.var(), &self.ts.and_defs, &mut depths);
            }
        }

        depths
    }

    /// Hash a literal with a seed for deterministic random ordering.
    pub(super) fn hash_lit_with_seed(lit: Lit, seed: u64) -> u64 {
        let mut z = (lit.code() as u64)
            .wrapping_add(seed)
            .wrapping_mul(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// MIC with explicit CTG parameters (for dynamic generalization).
    pub(super) fn mic_with_params(
        &mut self,
        frame: usize,
        cube: Vec<Lit>,
        dyn_ctg_max: usize,
        dyn_ctg_limit: usize,
    ) -> Vec<Lit> {
        let orig_ctg_max = self.config.ctg_max;
        let orig_ctg_limit = self.config.ctg_limit;
        self.config.ctg_max = dyn_ctg_max;
        self.config.ctg_limit = dyn_ctg_limit;
        let result = self.mic(frame, cube);
        self.config.ctg_max = orig_ctg_max;
        self.config.ctg_limit = orig_ctg_limit;
        result
    }

    /// Return a list of additional generalization orderings for multi-ordering lift.
    ///
    /// The first additional ordering is always the complement of the primary:
    /// Activity <-> ReverseTopological. The second (if requested) is RandomShuffle
    /// with a deterministic seed offset, providing pure diversity without heuristic bias.
    ///
    /// `count` is the number of ADDITIONAL orderings beyond the primary (so
    /// `multi_lift_orderings - 1`).
    pub(super) fn additional_orderings(&self, count: usize) -> Vec<GeneralizationOrder> {
        let mut orderings = Vec::with_capacity(count);
        if count == 0 {
            return orderings;
        }
        // First additional: complementary ordering.
        let complementary = match self.config.gen_order {
            GeneralizationOrder::Activity => GeneralizationOrder::ReverseTopological,
            GeneralizationOrder::ReverseTopological => GeneralizationOrder::Activity,
            GeneralizationOrder::RandomShuffle => GeneralizationOrder::Activity,
        };
        orderings.push(complementary);
        if count >= 2 {
            // Second additional: RandomShuffle (or Activity if primary is already random).
            let random_order = if self.config.gen_order == GeneralizationOrder::RandomShuffle {
                GeneralizationOrder::ReverseTopological
            } else {
                GeneralizationOrder::RandomShuffle
            };
            orderings.push(random_order);
        }
        // For count >= 3, we could add more, but 3 total orderings is the practical
        // maximum: Activity + ReverseTopological + RandomShuffle covers all axes.
        orderings
    }

    /// Compute the intersection of a cube with a parent lemma cube (CAV'23 #4150).
    ///
    /// Returns a reduced cube containing only literals present in both the current
    /// cube and the parent's blocking lemma (converted to cube form). If the
    /// intersection is empty or too small (< 2 literals), returns None to signal
    /// that the optimization should not be applied.
    ///
    /// The parent lemma's blocking clause is stored in negated form in the frame
    /// system. We look up the parent's cube in the frame system and compute the
    /// intersection with the current cube.
    fn parent_lemma_intersection(
        &self,
        cube: &[Lit],
        parent_cube: &[Lit],
        frame: usize,
    ) -> Option<Vec<Lit>> {
        // Look up the blocking lemma for the parent cube in the frame system.
        // The parent was blocked at frame or frame+1; search the current frame
        // and one level above.
        let parent_lemma_cube = self.frames.parent_lemma(parent_cube, frame)
            .or_else(|| {
                if frame + 1 <= self.frames.depth() {
                    self.frames.parent_lemma(parent_cube, frame + 1)
                } else {
                    None
                }
            });

        let parent_lemma_cube = parent_lemma_cube?;

        // Build a set from the parent lemma's cube literals for fast lookup.
        let parent_set: rustc_hash::FxHashSet<Lit> =
            parent_lemma_cube.into_iter().collect();

        // Intersection: keep only cube literals that appear in the parent lemma.
        let intersection: Vec<Lit> = cube.iter()
            .filter(|lit| parent_set.contains(lit))
            .copied()
            .collect();

        // Only use the intersection if it's meaningful (>= 2 literals and
        // strictly smaller than the original cube).
        if intersection.len() >= 2 && intersection.len() < cube.len() {
            Some(intersection)
        } else {
            None
        }
    }

    /// MIC with parent lemma seeding (CAV'23 #4150).
    ///
    /// When the proof obligation has a parent, uses the intersection of the
    /// current cube and the parent's blocking lemma as a tighter starting point
    /// for MIC. If the intersection is inductive, MIC runs on the smaller cube,
    /// producing tighter lemmas with fewer SAT calls. Falls back to standard
    /// MIC if the intersection is not available or not inductive.
    pub(super) fn mic_with_parent_seed(
        &mut self,
        frame: usize,
        cube: Vec<Lit>,
        parent_cube: Option<&[Lit]>,
    ) -> Vec<Lit> {
        if let Some(parent) = parent_cube {
            if let Some(seed) = self.parent_lemma_intersection(&cube, parent, frame) {
                // Verify the seed is inductive before using it.
                if self.is_inductive(frame, &seed) {
                    // The intersection is inductive — use it as the starting point.
                    // This produces a tighter lemma than starting from the full cube.
                    if std::env::var("IC3_DEBUG").is_ok() {
                        eprintln!(
                            "IC3 parent_lemma_mic: frame={} cube_len={} seed_len={} reduction={:.0}%",
                            frame,
                            cube.len(),
                            seed.len(),
                            (1.0 - seed.len() as f64 / cube.len() as f64) * 100.0,
                        );
                    }
                    return self.mic(frame, seed);
                }
            }
        }
        // Fallback: standard MIC on the original cube.
        self.mic(frame, cube)
    }

    /// MIC with parent lemma seeding and explicit CTG parameters (CAV'23 #4150).
    pub(super) fn mic_with_parent_seed_params(
        &mut self,
        frame: usize,
        cube: Vec<Lit>,
        parent_cube: Option<&[Lit]>,
        dyn_ctg_max: usize,
        dyn_ctg_limit: usize,
    ) -> Vec<Lit> {
        if let Some(parent) = parent_cube {
            if let Some(seed) = self.parent_lemma_intersection(&cube, parent, frame) {
                if self.is_inductive(frame, &seed) {
                    if std::env::var("IC3_DEBUG").is_ok() {
                        eprintln!(
                            "IC3 parent_lemma_mic: frame={} cube_len={} seed_len={} reduction={:.0}% (dynamic)",
                            frame,
                            cube.len(),
                            seed.len(),
                            (1.0 - seed.len() as f64 / cube.len() as f64) * 100.0,
                        );
                    }
                    return self.mic_with_params(frame, seed, dyn_ctg_max, dyn_ctg_limit);
                }
            }
        }
        self.mic_with_params(frame, cube, dyn_ctg_max, dyn_ctg_limit)
    }

    /// MIC with parent lemma seeding + multi-ordering lift (CAV'23 #4150 + #4099).
    pub(super) fn mic_multi_order_with_parent_seed(
        &mut self,
        frame: usize,
        cube: Vec<Lit>,
        parent_cube: Option<&[Lit]>,
    ) -> Vec<Lit> {
        if let Some(parent) = parent_cube {
            if let Some(seed) = self.parent_lemma_intersection(&cube, parent, frame) {
                if self.is_inductive(frame, &seed) {
                    if std::env::var("IC3_DEBUG").is_ok() {
                        eprintln!(
                            "IC3 parent_lemma_mic: frame={} cube_len={} seed_len={} reduction={:.0}% (multi-order)",
                            frame,
                            cube.len(),
                            seed.len(),
                            (1.0 - seed.len() as f64 / cube.len() as f64) * 100.0,
                        );
                    }
                    return self.mic_multi_order(frame, seed);
                }
            }
        }
        self.mic_multi_order(frame, cube)
    }

    /// MIC with parent lemma seeding + multi-ordering + dynamic CTG (CAV'23 #4150 + #4099).
    pub(super) fn mic_multi_order_with_parent_seed_params(
        &mut self,
        frame: usize,
        cube: Vec<Lit>,
        parent_cube: Option<&[Lit]>,
        dyn_ctg_max: usize,
        dyn_ctg_limit: usize,
    ) -> Vec<Lit> {
        if let Some(parent) = parent_cube {
            if let Some(seed) = self.parent_lemma_intersection(&cube, parent, frame) {
                if self.is_inductive(frame, &seed) {
                    if std::env::var("IC3_DEBUG").is_ok() {
                        eprintln!(
                            "IC3 parent_lemma_mic: frame={} cube_len={} seed_len={} reduction={:.0}% (multi-order+dynamic)",
                            frame,
                            cube.len(),
                            seed.len(),
                            (1.0 - seed.len() as f64 / cube.len() as f64) * 100.0,
                        );
                    }
                    return self.mic_multi_order_with_params(frame, seed, dyn_ctg_max, dyn_ctg_limit);
                }
            }
        }
        self.mic_multi_order_with_params(frame, cube, dyn_ctg_max, dyn_ctg_limit)
    }

    /// MIC with multi-ordering lift (#4099).
    ///
    /// Runs MIC with the primary ordering, then tries additional orderings if the
    /// result isn't tight enough (> half original cube length) and the circuit is
    /// large enough (> 15 latches). Keeps the shortest result across all orderings.
    pub(super) fn mic_multi_order(&mut self, frame: usize, cube: Vec<Lit>) -> Vec<Lit> {
        if self.config.ctg_down {
            return self.mic(frame, cube);
        }

        let original_len = cube.len();
        let orderings_count = self.config.multi_lift_orderings.saturating_sub(1);
        let additional = self.additional_orderings(orderings_count);

        // Pass 1: primary ordering.
        let mut best = self.mic(frame, cube.clone());

        // Additional passes: only attempted when the best result isn't tight.
        if best.len() > original_len / 2 && self.ts.latch_vars.len() > 15 {
            let orig_order = self.config.gen_order;
            let orig_seed = self.config.random_seed;

            for alt_order in &additional {
                self.config.gen_order = *alt_order;
                // Use a deterministic seed offset for RandomShuffle diversity.
                if *alt_order == GeneralizationOrder::RandomShuffle {
                    self.config.random_seed = orig_seed.wrapping_add(0x4099);
                }

                let candidate = self.mic(frame, cube.clone());
                if candidate.len() < best.len() {
                    best = candidate;
                    // If we found a tight result, stop early.
                    if best.len() <= original_len / 2 {
                        break;
                    }
                }
            }

            self.config.gen_order = orig_order;
            self.config.random_seed = orig_seed;
        }

        if std::env::var("IC3_DEBUG").is_ok() && orderings_count > 0 {
            eprintln!(
                "IC3 multi_order: frame={} original={} result={} orderings_tried={}",
                frame, original_len, best.len(),
                if best.len() > original_len / 2 { orderings_count + 1 } else { 1 },
            );
        }

        best
    }

    /// MIC with multi-ordering lift and explicit CTG parameters (#4099).
    pub(super) fn mic_multi_order_with_params(
        &mut self,
        frame: usize,
        cube: Vec<Lit>,
        dyn_ctg_max: usize,
        dyn_ctg_limit: usize,
    ) -> Vec<Lit> {
        if self.config.ctg_down {
            return self.mic_with_params(frame, cube, dyn_ctg_max, dyn_ctg_limit);
        }

        let original_len = cube.len();
        let orderings_count = self.config.multi_lift_orderings.saturating_sub(1);
        let additional = self.additional_orderings(orderings_count);

        // Pass 1: primary ordering.
        let mut best = self.mic_with_params(frame, cube.clone(), dyn_ctg_max, dyn_ctg_limit);

        // Additional passes: only attempted when the best result isn't tight.
        if best.len() > original_len / 2 && self.ts.latch_vars.len() > 15 {
            let orig_order = self.config.gen_order;
            let orig_seed = self.config.random_seed;

            for alt_order in &additional {
                self.config.gen_order = *alt_order;
                if *alt_order == GeneralizationOrder::RandomShuffle {
                    self.config.random_seed = orig_seed.wrapping_add(0x4099);
                }

                let candidate = self.mic_with_params(frame, cube.clone(), dyn_ctg_max, dyn_ctg_limit);
                if candidate.len() < best.len() {
                    best = candidate;
                    if best.len() <= original_len / 2 {
                        break;
                    }
                }
            }

            self.config.gen_order = orig_order;
            self.config.random_seed = orig_seed;
        }

        best
    }

    /// MIC: Minimal Inductive Clause generalization with CTG.
    pub(super) fn mic(&mut self, frame: usize, cube: Vec<Lit>) -> Vec<Lit> {
        if self.config.ctg_down {
            return self.mic_ctg_down(frame, cube);
        }

        let orig_cube = cube.clone();
        let mut result = cube;

        let mut domain_solver = self.build_mic_domain_solver(frame, &result);

        // Phase 1: Core-based initial reduction.
        let core_reduced = if let Some(ref mut ds) = domain_solver {
            self.is_inductive_with_core_on_solver(ds.as_mut(), &result)
        } else {
            self.is_inductive_with_core(frame, &result)
        };
        if let Some(core_reduced) = core_reduced {
            if core_reduced.len() < result.len() {
                result = core_reduced;
                if domain_solver.is_some() {
                    domain_solver = self.build_mic_domain_solver(frame, &result);
                }
            }
        }

        if result.len() <= 2 {
            // SOUNDNESS FIX (#4092): Even small cubes from core reduction can
            // be unsound if z4-sat produced a false UNSAT core. Verify before
            // returning.
            if self.cube_sat_consistent_with_init(&result) {
                result = orig_cube.clone();
            } else if result.len() < orig_cube.len()
                && self.ts.latch_vars.len() <= 60
                && !self.verify_consecution_independent(frame, &result, true)
            {
                result = orig_cube;
            }
            self.bump_activity(&result);
            self.decay_activity();
            return result;
        }

        // Phase 2: Generalization-order-sorted backward iteration with CTG.
        self.sort_for_generalization(&mut result);

        // Phase 2b: Parent lemma heuristic (CAV'23).
        //
        // Sort literals so parent-lemma literals are at the FRONT. MIC's
        // backward iteration (while i > 0 { i -= 1 }) tries to remove
        // literals from the END first, so literals at the FRONT are tried
        // for removal LAST — preserving parent structure in the generalized
        // clause. Non-parent literals (at the back) are tried first, which
        // is what we want: they're less likely to be in the inductive core.
        if self.config.parent_lemma {
            if let Some(parent_cube) = self.frames.parent_lemma(&result, frame) {
                let parent_set: rustc_hash::FxHashSet<Lit> =
                    parent_cube.into_iter().collect();
                // Stable sort: parent literals (true→false=0) at front,
                // non-parent (false→true=1) at back. Within each group,
                // the generalization order from Phase 2 is preserved.
                result.sort_by_key(|lit| !parent_set.contains(lit));
            }
        }

        let budget = self.config.mic_drop_budget;
        let mut drop_calls = 0usize;
        let mut i = result.len();
        while i > 0 {
            i -= 1;
            if result.len() <= 1 {
                break;
            }
            if budget > 0 && drop_calls >= budget {
                break;
            }
            let mut candidate = result.clone();
            candidate.remove(i);
            let is_ind = if let Some(ref mut ds) = domain_solver {
                self.is_inductive_on_solver(ds.as_mut(), &candidate)
            } else {
                self.is_inductive(frame, &candidate)
            };
            drop_calls += 1;
            if is_ind {
                result = candidate;
            } else if frame > 1 {
                let mut ctg_count = 0;
                let mut dropped = false;
                while ctg_count < self.config.ctg_max {
                    let pred = if let Some(ref ds) = domain_solver {
                        self.extract_full_state_from_solver(ds.as_ref())
                    } else {
                        self.extract_full_state_from_solver(self.solvers[frame - 1].as_ref())
                    };
                    if self.cube_consistent_with_init(&pred) {
                        break;
                    }
                    let lemma_snapshot: Vec<usize> = if domain_solver.is_some() {
                        self.frames.frames.iter().map(|f| f.lemmas.len()).collect()
                    } else {
                        Vec::new()
                    };
                    let inf_count = if domain_solver.is_some() {
                        self.inf_lemmas.len()
                    } else {
                        0
                    };
                    let mut tb_limit = self.config.ctg_limit;
                    if !self.trivial_block(frame - 1, pred, &mut tb_limit) {
                        break;
                    }
                    ctg_count += 1;
                    drop_calls += 1;
                    if let Some(ref mut ds) = domain_solver {
                        let domain_set = self
                            .domain_computer
                            .compute_domain(&result, &self.next_vars);
                        for (f_idx, &old_count) in lemma_snapshot.iter().enumerate() {
                            if f_idx < self.frames.frames.len() {
                                for lemma in &self.frames.frames[f_idx].lemmas[old_count..] {
                                    if lemma.lits.iter().any(|l| domain_set.contains(l.var())) {
                                        ds.add_clause(&lemma.lits);
                                    }
                                }
                            }
                        }
                        for lemma in &self.inf_lemmas[inf_count..] {
                            if lemma.lits.iter().any(|l| domain_set.contains(l.var())) {
                                ds.add_clause(&lemma.lits);
                            }
                        }
                    }
                    let retry_ind = if let Some(ref mut ds) = domain_solver {
                        self.is_inductive_on_solver(ds.as_mut(), &candidate)
                    } else {
                        self.is_inductive(frame, &candidate)
                    };
                    drop_calls += 1;
                    if retry_ind {
                        result = candidate;
                        dropped = true;
                        break;
                    }
                }
                if !dropped {
                    // Literal is essential — keep it.
                }
            }
        }
        // SOUNDNESS FIX (#4092): Final init-consistency guard.
        // After all generalization steps, verify the result is not init-consistent.
        // If it is, fall back to the original cube. This matches rIC3's pattern
        // of checking cube_subsume_init at every iteration in down()/ctg_down().
        if self.cube_sat_consistent_with_init(&result) {
            result = orig_cube.clone();
        }
        // SOUNDNESS FIX (#4092): Final inductiveness verification.
        // z4-sat false UNSAT in is_inductive() can cause MIC to drop literals
        // that are actually essential, producing non-inductive cubes. Cross-check
        // with an independent SimpleSolver to catch these cases.
        if result.len() < orig_cube.len() && self.ts.latch_vars.len() <= 60 {
            if !self.verify_consecution_independent(frame, &result, true) {
                result = orig_cube;
            }
        }
        self.bump_activity(&result);
        self.decay_activity();
        result
    }

    /// CTG-enhanced down() MIC variant with (s,t) counterexample caching.
    pub(super) fn mic_ctg_down(&mut self, frame: usize, cube: Vec<Lit>) -> Vec<Lit> {
        let orig_cube = cube.clone();
        let mut result = cube;

        let mut domain_solver = self.build_mic_domain_solver(frame, &result);

        // Phase 1: Core-based initial reduction.
        let core_reduced = if let Some(ref mut ds) = domain_solver {
            self.is_inductive_with_core_on_solver(ds.as_mut(), &result)
        } else {
            self.is_inductive_with_core(frame, &result)
        };
        if let Some(core_reduced) = core_reduced {
            if core_reduced.len() < result.len() {
                result = core_reduced;
                if domain_solver.is_some() {
                    domain_solver = self.build_mic_domain_solver(frame, &result);
                }
            }
        }

        // Phase 2: Generalization-order sort + parent lemma heuristic.
        self.sort_for_generalization(&mut result);
        // Phase 2b: Parent lemma heuristic for CTG-down (CAV'23).
        //
        // CTG-down uses FORWARD iteration (while i < result.len()), so
        // literals at the FRONT are tried for removal FIRST. We want
        // non-parent literals tried first (they're less likely to be in
        // the inductive core), so put them at the front (false=0) and
        // parent literals at the back (true=1) — tried last, preserving
        // parent structure.
        if self.config.parent_lemma {
            if let Some(parent_cube) = self.frames.parent_lemma(&result, frame) {
                let parent_set: rustc_hash::FxHashSet<Lit> =
                    parent_cube.into_iter().collect();
                result.sort_by_key(|lit| parent_set.contains(lit));
            }
        }

        // Phase 3: CTG-down literal dropping with (s,t) cex caching.
        let mut keep = rustc_hash::FxHashSet::default();
        let mut cex_cache: Vec<(Lemma, Lemma)> = Vec::new();
        let budget = self.config.mic_drop_budget;
        let mut drop_calls = 0usize;
        let mut i = 0;
        while i < result.len() {
            if result.len() <= 1 {
                break;
            }
            if budget > 0 && drop_calls >= budget {
                break;
            }
            if keep.contains(&result[i]) {
                i += 1;
                continue;
            }

            let mut candidate = result.clone();
            candidate.remove(i);

            // (s,t) cex cache check.
            let candidate_lemma = Lemma::from_blocked_cube(&candidate);
            let cex_hit = cex_cache.iter().any(|(s, t)| {
                !candidate_lemma.subsumes(s) && candidate_lemma.subsumes(t)
            });
            if cex_hit {
                keep.insert(result[i]);
                i += 1;
                continue;
            }

            let is_ind = if let Some(ref mut ds) = domain_solver {
                self.is_inductive_on_solver(ds.as_mut(), &candidate)
            } else {
                self.is_inductive(frame, &candidate)
            };
            drop_calls += 1;
            if is_ind {
                result = candidate;
                continue;
            }

            // Drop failed — attempt CTG-down shrinking.
            if frame > 1 {
                let mut ctg_count = 0;
                let mut shrunk = false;

                loop {
                    let mut keep_violated = false;
                    let solver_ref: &dyn SatSolver = if let Some(ref ds) = domain_solver {
                        ds.as_ref()
                    } else {
                        self.solvers[frame - 1].as_ref()
                    };
                    for &k in &keep {
                        if let Some(val) = solver_ref.value(k) {
                            if !val {
                                keep_violated = true;
                                break;
                            }
                        }
                    }
                    if keep_violated {
                        break;
                    }

                    let pred = self.extract_full_state_from_solver(solver_ref);

                    if ctg_count < self.config.ctg_max
                        && !self.cube_consistent_with_init(&pred)
                    {
                        let lemma_snapshot: Vec<usize> = if domain_solver.is_some() {
                            self.frames.frames.iter().map(|f| f.lemmas.len()).collect()
                        } else {
                            Vec::new()
                        };
                        let inf_count = if domain_solver.is_some() {
                            self.inf_lemmas.len()
                        } else {
                            0
                        };

                        let mut tb_limit = self.config.ctg_limit;
                        if !self.trivial_block(frame - 1, pred.clone(), &mut tb_limit) {
                            // Fall through to model-based shrinking below.
                        } else {
                            ctg_count += 1;
                            if let Some(ref mut ds) = domain_solver {
                                let domain_set = self
                                    .domain_computer
                                    .compute_domain(&result, &self.next_vars);
                                for (f_idx, &old_count) in lemma_snapshot.iter().enumerate() {
                                    if f_idx < self.frames.frames.len() {
                                        for lemma in &self.frames.frames[f_idx].lemmas[old_count..] {
                                            if lemma.lits.iter().any(|l| domain_set.contains(l.var())) {
                                                ds.add_clause(&lemma.lits);
                                            }
                                        }
                                    }
                                }
                                for lemma in &self.inf_lemmas[inf_count..] {
                                    if lemma.lits.iter().any(|l| domain_set.contains(l.var())) {
                                        ds.add_clause(&lemma.lits);
                                    }
                                }
                            }
                            let retry_ind = if let Some(ref mut ds) = domain_solver {
                                self.is_inductive_on_solver(ds.as_mut(), &candidate)
                            } else {
                                self.is_inductive(frame, &candidate)
                            };
                            if retry_ind {
                                result = candidate;
                                shrunk = true;
                                break;
                            }
                            continue;
                        }
                    }

                    // Model-based shrinking with flip_to_none (#4091 Phase 3).
                    let model_solver: &mut dyn SatSolver = if let Some(ref mut ds) = domain_solver {
                        ds.as_mut()
                    } else {
                        self.solvers[frame - 1].as_mut()
                    };
                    let model_set: rustc_hash::FxHashSet<Lit> = result
                        .iter()
                        .filter(|&&lit| {
                            model_solver
                                .value(lit)
                                .unwrap_or(false)
                        })
                        .copied()
                        .collect();

                    let use_flip = self.config.flip_to_none_lift;

                    // Cache (s,t) counterexample pair.
                    {
                        let s_lits: Vec<Lit> = if use_flip {
                            self.ts.latch_vars.iter().filter_map(|&lv| {
                                let lit = Lit::pos(lv);
                                if let Some(v) = model_solver.value(lit) {
                                    if model_solver.flip_to_none(lv) {
                                        Some(if v { Lit::pos(lv) } else { Lit::neg(lv) })
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            }).collect()
                        } else {
                            self.ts.latch_vars.iter().filter_map(|&lv| {
                                model_solver.value(Lit::pos(lv)).map(|val| {
                                    if val { Lit::pos(lv) } else { Lit::neg(lv) }
                                })
                            }).collect()
                        };
                        let t_lits: Vec<Lit> = self.ts.latch_vars.iter().filter_map(|&lv| {
                            if let Some(&next_var) = self.next_vars.get(&lv) {
                                model_solver.value(Lit::pos(next_var)).map(|val| {
                                    if val { Lit::pos(lv) } else { Lit::neg(lv) }
                                })
                            } else {
                                None
                            }
                        }).collect();
                        if !s_lits.is_empty() && !t_lits.is_empty() {
                            cex_cache.push((Lemma::new(s_lits), Lemma::new(t_lits)));
                        }
                    }

                    let new_result: Vec<Lit> = result
                        .iter()
                        .filter(|lit| {
                            if keep.contains(lit) {
                                true
                            } else if model_set.contains(lit) {
                                if use_flip {
                                    !model_solver.flip_to_none(lit.var())
                                } else {
                                    true
                                }
                            } else {
                                false
                            }
                        })
                        .copied()
                        .collect();

                    // SOUNDNESS FIX (#4092): Reject model-based shrink results
                    // that are init-consistent. rIC3's down()/ctg_down() check
                    // cube_subsume_init at the top of every iteration; our
                    // model-based shrinking bypasses is_inductive() and could
                    // produce a cube that overlaps with initial states.
                    if !new_result.is_empty()
                        && new_result.len() < result.len()
                        && !self.cube_sat_consistent_with_init(&new_result)
                    {
                        result = new_result;
                        if domain_solver.is_some() {
                            domain_solver = self.build_mic_domain_solver(frame, &result);
                        }
                        i = 0;
                        shrunk = true;
                    }
                    break;
                }

                if !shrunk {
                    keep.insert(result[i]);
                    i += 1;
                }
            } else {
                keep.insert(result[i]);
                i += 1;
            }
        }

        // SOUNDNESS FIX (#4092): Final init-consistency guard.
        if self.cube_sat_consistent_with_init(&result) {
            result = orig_cube.clone();
        }
        // SOUNDNESS FIX (#4092): Final inductiveness verification.
        if result.len() < orig_cube.len() && self.ts.latch_vars.len() <= 60 {
            if !self.verify_consecution_independent(frame, &result, true) {
                result = orig_cube;
            }
        }
        self.bump_activity(&result);
        self.decay_activity();
        result
    }

    /// Try to block a cube at the given frame with count-limited recursion.
    pub(super) fn trivial_block(&mut self, frame: usize, cube: Vec<Lit>, limit: &mut usize) -> bool {
        if frame == 0 || *limit == 0 {
            return false;
        }
        if self.cube_sat_consistent_with_init(&cube) {
            return false;
        }
        *limit -= 1;
        loop {
            if self.is_inductive(frame, &cube) {
                let generalized = self.mic_simple(frame, cube);
                // SOUNDNESS FIX (#4092): Reject init-consistent generalizations.
                // mic_simple() can over-generalize by dropping literals, producing
                // a cube that overlaps with initial states. Without this check,
                // the unsound lemma enters the frame system through push_lemma()
                // and poisons all frame solvers, leading to false UNSAT.
                // rIC3 checks cube_subsume_init in trivial_block before mic.
                if self.cube_sat_consistent_with_init(&generalized) {
                    return false;
                }
                let (push_frame, pushed_cube) = self.push_lemma(frame, generalized);
                let lemma_idx = (push_frame - 1).min(self.frames.depth() - 1);
                let lemma = Lemma::from_blocked_cube(&pushed_cube);
                self.frames.add_lemma(lemma_idx, lemma.clone());
                let start = if lemma_idx == 0 { 0 } else { 1 };
                for s in &mut self.solvers[start..=lemma_idx] {
                    s.add_clause(&lemma.lits);
                }
                return true;
            }
            if *limit == 0 {
                return false;
            }
            let pred = self.extract_full_state_from_solver(self.solvers[frame - 1].as_ref());
            if !self.trivial_block(frame - 1, pred, limit) {
                return false;
            }
        }
    }

    /// Simple MIC without CTG (used inside trivial_block to avoid recursion).
    pub(super) fn mic_simple(&mut self, frame: usize, cube: Vec<Lit>) -> Vec<Lit> {
        let orig_cube = cube.clone();
        let mut result = cube;

        let mut domain_solver = self.build_mic_domain_solver(frame, &result);

        let core_reduced = if let Some(ref mut ds) = domain_solver {
            self.is_inductive_with_core_on_solver(ds.as_mut(), &result)
        } else {
            self.is_inductive_with_core(frame, &result)
        };
        if let Some(core_reduced) = core_reduced {
            if core_reduced.len() < result.len() {
                result = core_reduced;
                if domain_solver.is_some() {
                    domain_solver = self.build_mic_domain_solver(frame, &result);
                }
            }
        }
        let budget = self.config.mic_drop_budget;
        let mut drop_calls = 0usize;
        let mut i = result.len();
        while i > 0 {
            i -= 1;
            if result.len() <= 1 {
                break;
            }
            if budget > 0 && drop_calls >= budget {
                break;
            }
            let mut candidate = result.clone();
            candidate.remove(i);
            let is_ind = if let Some(ref mut ds) = domain_solver {
                self.is_inductive_on_solver(ds.as_mut(), &candidate)
            } else {
                self.is_inductive(frame, &candidate)
            };
            drop_calls += 1;
            if is_ind {
                result = candidate;
            }
        }
        // SOUNDNESS FIX (#4092): Final init-consistency guard.
        if self.cube_sat_consistent_with_init(&result) {
            result = orig_cube.clone();
        }
        // SOUNDNESS FIX (#4092): Final inductiveness verification.
        if result.len() < orig_cube.len() && self.ts.latch_vars.len() <= 60 {
            if !self.verify_consecution_independent(frame, &result, true) {
                result = orig_cube;
            }
        }
        result
    }

    /// Check if a cube is inductive relative to frame[frame-1] with !cube strengthening.
    pub(super) fn is_inductive(&mut self, frame: usize, cube: &[Lit]) -> bool {
        if frame == 0 {
            return false;
        }
        if self.cube_sat_consistent_with_init(cube) {
            return false;
        }
        let solver_idx = frame - 1;
        if solver_idx >= self.solvers.len() {
            return false;
        }
        if self.solvers[solver_idx].is_poisoned() {
            self.rebuild_solver_at(solver_idx);
        }
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        let assumptions = self.prime_cube(cube);
        self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube)
            == SatResult::Unsat
    }

    /// Check inductiveness and return the UNSAT core-reduced cube if inductive.
    pub(super) fn is_inductive_with_core(&mut self, frame: usize, cube: &[Lit]) -> Option<Vec<Lit>> {
        if frame == 0 {
            return None;
        }
        if self.cube_sat_consistent_with_init(cube) {
            return None;
        }
        let solver_idx = frame - 1;
        if solver_idx >= self.solvers.len() {
            return None;
        }
        if self.solvers[solver_idx].is_poisoned() {
            self.rebuild_solver_at(solver_idx);
        }
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        let assumptions = self.prime_cube(cube);
        let result = self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube);
        if result != SatResult::Unsat {
            return None;
        }
        let Some(core) = self.solvers[solver_idx].unsat_core() else {
            return Some(cube.to_vec());
        };
        if core.is_empty() {
            return Some(cube.to_vec());
        }
        let mut core_latch_vars = rustc_hash::FxHashSet::default();
        for &core_lit in &core {
            if let Some(&latch_var) = self.reverse_next.get(&core_lit.var()) {
                core_latch_vars.insert(latch_var);
            }
        }
        let reduced: Vec<Lit> = cube
            .iter()
            .filter(|lit| core_latch_vars.contains(&lit.var()))
            .copied()
            .collect();
        if reduced.is_empty() {
            return Some(cube.to_vec());
        }
        // SOUNDNESS FIX (#4092): Use precise SAT-based init check instead
        // of the fast over-approximation. For circuits with non-unit init
        // clauses (e.g., microban benchmarks with 100+ constraints), the
        // fast check may miss init-consistency, allowing a reduced cube that
        // overlaps with initial states to be accepted.
        if self.cube_sat_consistent_with_init(&reduced) {
            Some(cube.to_vec())
        } else {
            Some(reduced)
        }
    }

    /// Check inductiveness using a domain-restricted solver.
    pub(super) fn is_inductive_on_solver(
        &self,
        solver: &mut dyn SatSolver,
        cube: &[Lit],
    ) -> bool {
        if self.cube_sat_consistent_with_init(cube) {
            return false;
        }
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        let assumptions = self.prime_cube(cube);
        solver.solve_with_temporary_clause(&assumptions, &neg_cube) == SatResult::Unsat
    }

    /// Check inductiveness with UNSAT core on a domain-restricted solver.
    pub(super) fn is_inductive_with_core_on_solver(
        &self,
        solver: &mut dyn SatSolver,
        cube: &[Lit],
    ) -> Option<Vec<Lit>> {
        if self.cube_sat_consistent_with_init(cube) {
            return None;
        }
        let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
        let assumptions = self.prime_cube(cube);
        let result = solver.solve_with_temporary_clause(&assumptions, &neg_cube);
        if result != SatResult::Unsat {
            return None;
        }
        let Some(core) = solver.unsat_core() else {
            return Some(cube.to_vec());
        };
        if core.is_empty() {
            return Some(cube.to_vec());
        }
        let mut core_latch_vars = rustc_hash::FxHashSet::default();
        for &core_lit in &core {
            if let Some(&latch_var) = self.reverse_next.get(&core_lit.var()) {
                core_latch_vars.insert(latch_var);
            }
        }
        let reduced: Vec<Lit> = cube
            .iter()
            .filter(|lit| core_latch_vars.contains(&lit.var()))
            .copied()
            .collect();
        if reduced.is_empty() {
            return Some(cube.to_vec());
        }
        // SOUNDNESS FIX (#4092): Use precise SAT-based init check.
        if self.cube_sat_consistent_with_init(&reduced) {
            Some(cube.to_vec())
        } else {
            Some(reduced)
        }
    }

    /// Build a domain-restricted solver for MIC operations on a given cube.
    pub(super) fn build_mic_domain_solver(
        &mut self,
        frame: usize,
        cube: &[Lit],
    ) -> Option<Box<dyn SatSolver>> {
        let domain = self
            .domain_computer
            .compute_domain(cube, &self.next_vars);

        let result = domain::build_domain_restricted_solver(
            &domain,
            &self.ts,
            &self.next_link_clauses,
            &self.frames.frames,
            frame.saturating_sub(1),
            &self.inf_lemmas,
            self.solver_backend,
            self.max_var,
        );

        self.domain_stats.record_mic(result.is_some());
        result
    }

    /// Build a domain-restricted solver for consecution checks (#4059, #4091).
    ///
    /// Threshold: >= 20 latches. The attempt to lower to >= 2 (#4091) caused
    /// IC3 to generate unsound invariants on small circuits — domain restriction
    /// skips clauses needed for soundness, particularly on high-constraint-ratio
    /// circuits (microban family, qspiflash). Reverted per Wave 15 results
    /// (15/50, regression from 24/50). The validation check caught the unsoundness
    /// (0 wrong answers) but the result was excessive timeouts.
    pub(super) fn build_consecution_domain_solver(
        &self,
        frame: usize,
        cube: &[Lit],
    ) -> Option<Box<dyn SatSolver>> {
        if self.ts.latch_vars.len() < 20 {
            return None;
        }

        let domain = self
            .domain_computer
            .compute_domain(cube, &self.next_vars);

        domain::build_domain_restricted_solver(
            &domain,
            &self.ts,
            &self.next_link_clauses,
            &self.frames.frames,
            frame.saturating_sub(1),
            &self.inf_lemmas,
            self.solver_backend,
            self.max_var,
        )
    }

    /// Log domain restriction statistics at IC3 completion (#4059).
    pub(super) fn log_domain_stats(&self) {
        let stats = &self.domain_stats;
        let consec_total = stats.total_attempts();
        let mic_total = stats.total_mic_attempts();
        if consec_total > 0 || mic_total > 0 {
            let restriction_rate = if consec_total > 0 {
                stats.restricted_count as f64 / consec_total as f64 * 100.0
            } else {
                0.0
            };
            let mic_rate = if mic_total > 0 {
                stats.mic_restricted as f64 / mic_total as f64 * 100.0
            } else {
                0.0
            };
            eprintln!(
                "IC3 domain stats: consecution(restricted={} fallback={} rate={:.1}%) \
                 mic(restricted={} fallback={} rate={:.1}%) \
                 avg_coverage={:.1}%",
                stats.restricted_count,
                stats.fallback_count,
                restriction_rate,
                stats.mic_restricted,
                stats.mic_fallback,
                mic_rate,
                stats.avg_coverage() * 100.0,
            );
        }
        if self.po_drop_count > 0 {
            eprintln!(
                "IC3 drop_po stats: {} POs dropped (threshold={:.1})",
                self.po_drop_count, self.config.drop_po_threshold,
            );
        }
    }
}

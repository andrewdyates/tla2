// Copyright 2026 Dropbox
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

    /// Sort MIC literals for a FORWARD-iteration caller (`mic_ctg_down`).
    ///
    /// Forward iteration (i=0..len) tries to drop literals at the FRONT first.
    /// To drop low-activity literals first (the rIC3 pattern at
    /// `ric3/src/ic3/mic.rs:225` — `sort_by_activity(&mut cube, true)` with
    /// `ascending=true`), we place low-activity literals at the FRONT.
    /// This inverts the direction of `sort_for_generalization` (which sorts
    /// high-activity to front for BACKWARD-iteration callers).
    ///
    /// ReverseTopological and RandomShuffle behave the same regardless of
    /// iteration direction — only the activity axis has a natural direction.
    pub(super) fn sort_for_generalization_forward(&self, lits: &mut [Lit]) {
        if self.config.internal_signals && !self.ts.internal_signals.is_empty() {
            // Phase 1: Partition internal signals to front (same as backward).
            let isig_set: rustc_hash::FxHashSet<Var> =
                self.ts.internal_signals.iter().copied().collect();
            lits.sort_by(|a, b| {
                let a_isig = isig_set.contains(&a.var());
                let b_isig = isig_set.contains(&b.var());
                (!a_isig).cmp(&(!b_isig))
            });
            let isig_count = lits.iter().filter(|l| isig_set.contains(&l.var())).count();
            let (isig_part, latch_part) = lits.split_at_mut(isig_count);
            self.sort_group_forward(isig_part);
            self.sort_group_forward(latch_part);
        } else {
            self.sort_group_forward(lits);
        }
    }

    /// Sort a slice of MIC literals for forward iteration (inverted activity).
    fn sort_group_forward(&self, lits: &mut [Lit]) {
        match self.config.gen_order {
            GeneralizationOrder::Activity => {
                // Ascending: low-activity at front, tried first by forward iter.
                // Matches rIC3 `mic.rs:225` — ascending=true.
                self.vsids.sort_by_activity_ascending(lits);
            }
            GeneralizationOrder::ReverseTopological => {
                // Same as backward path: literals further from inputs first.
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
        let parent_lemma_cube = self.frames.parent_lemma(parent_cube, frame).or_else(|| {
            if frame + 1 <= self.frames.depth() {
                self.frames.parent_lemma(parent_cube, frame + 1)
            } else {
                None
            }
        });

        let parent_lemma_cube = parent_lemma_cube?;

        // Build a set from the parent lemma's cube literals for fast lookup.
        let parent_set: rustc_hash::FxHashSet<Lit> = parent_lemma_cube.into_iter().collect();

        // Intersection: keep only cube literals that appear in the parent lemma.
        let intersection: Vec<Lit> = cube
            .iter()
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
                    return self.mic_multi_order_with_params(
                        frame,
                        seed,
                        dyn_ctg_max,
                        dyn_ctg_limit,
                    );
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
    ///
    /// Time budget: each additional ordering is capped at 2x the wall-clock time
    /// of the first pass. This prevents multi-ordering from dominating IC3 runtime
    /// on circuits where MIC is expensive (many latches, deep CTG chains).
    pub(super) fn mic_multi_order(&mut self, frame: usize, cube: Vec<Lit>) -> Vec<Lit> {
        if self.config.ctg_down {
            return self.mic(frame, cube);
        }

        let original_len = cube.len();
        let orderings_count = self.config.multi_lift_orderings.saturating_sub(1);
        let additional = self.additional_orderings(orderings_count);

        // Pass 1: primary ordering (timed for budget calculation).
        let t0 = std::time::Instant::now();
        let mut best = self.mic(frame, cube.clone());
        let first_pass_elapsed = t0.elapsed();
        // Budget: additional orderings get at most 2x first pass time total.
        let time_budget = first_pass_elapsed * 2;

        // Additional passes: only attempted when the best result isn't tight.
        if best.len() > original_len / 2 && self.ts.latch_vars.len() > 15 {
            let orig_order = self.config.gen_order;
            let orig_seed = self.config.random_seed;
            let extra_start = std::time::Instant::now();

            for alt_order in &additional {
                // Time budget check: stop if additional passes exceed 2x first pass.
                if extra_start.elapsed() > time_budget {
                    break;
                }

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
                "IC3 multi_order: frame={} original={} result={} orderings_tried={} first_pass={:?}",
                frame, original_len, best.len(),
                if best.len() > original_len / 2 { orderings_count + 1 } else { 1 },
                first_pass_elapsed,
            );
        }

        best
    }

    /// MIC with multi-ordering lift and explicit CTG parameters (#4099).
    ///
    /// Same as `mic_multi_order` but with dynamic CTG parameters. Time budget
    /// of 2x first pass applies to additional orderings.
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

        // Pass 1: primary ordering (timed for budget calculation).
        let t0 = std::time::Instant::now();
        let mut best = self.mic_with_params(frame, cube.clone(), dyn_ctg_max, dyn_ctg_limit);
        let first_pass_elapsed = t0.elapsed();
        let time_budget = first_pass_elapsed * 2;

        // Additional passes: only attempted when the best result isn't tight.
        if best.len() > original_len / 2 && self.ts.latch_vars.len() > 15 {
            let orig_order = self.config.gen_order;
            let orig_seed = self.config.random_seed;
            let extra_start = std::time::Instant::now();

            for alt_order in &additional {
                if extra_start.elapsed() > time_budget {
                    break;
                }

                self.config.gen_order = *alt_order;
                if *alt_order == GeneralizationOrder::RandomShuffle {
                    self.config.random_seed = orig_seed.wrapping_add(0x4099);
                }

                let candidate =
                    self.mic_with_params(frame, cube.clone(), dyn_ctg_max, dyn_ctg_limit);
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
        // #4288: Validate core reduction with independent cross-check before
        // accepting. z4-sat's unsat_core can be unsound.
        let core_reduced = if let Some(ref mut ds) = domain_solver {
            self.is_inductive_with_core_on_solver(ds.as_mut(), &result)
        } else {
            self.is_inductive_with_core(frame, &result)
        };
        if let Some(core_reduced) = core_reduced {
            if core_reduced.len() < result.len() {
                let accept = if self.ts.latch_vars.len() <= 60 {
                    self.verify_consecution_independent(frame, &core_reduced, true)
                } else {
                    true
                };
                if accept {
                    result = core_reduced;
                    if domain_solver.is_some() {
                        domain_solver = self.build_mic_domain_solver(frame, &result);
                    }
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
                let parent_set: rustc_hash::FxHashSet<Lit> = parent_cube.into_iter().collect();
                // Stable sort: parent literals (true→false=0) at front,
                // non-parent (false→true=1) at back. Within each group,
                // the generalization order from Phase 2 is preserved.
                result.sort_by_key(|lit| !parent_set.contains(lit));
            }
        }

        let budget = self.config.mic_drop_budget;
        let mic_attempts = self.config.mic_attempts;
        let mut drop_calls = 0usize;
        let mut consecutive_failures = 0usize;
        let mut i = result.len();
        while i > 0 {
            i -= 1;
            if result.len() <= 1 {
                break;
            }
            if budget > 0 && drop_calls >= budget {
                break;
            }
            // Consecutive failure early abort (#4244, IC3ref micAttempts).
            // If mic_attempts consecutive literals cannot be dropped, the cube
            // is approximately minimal — stop trying. Dramatically improves
            // mics/second on circuits where most literals are essential.
            if mic_attempts > 0 && consecutive_failures >= mic_attempts {
                break;
            }
            // Cooperative cancellation (#4096): MIC backward iteration can
            // make hundreds of SAT calls. Check cancellation each iteration
            // so the portfolio thread exits promptly after timeout.
            if self.is_cancelled() {
                break;
            }
            let mut candidate = result.clone();
            candidate.remove(i);
            // #4288: Use UNSAT-core reduction on every successful drop
            // (rIC3 mic.rs:84 returns `inductive_core()` from `down()`, and
            // handle_down_success filters the cube by the core). This lets a
            // single drop remove MULTIPLE literals when the SAT solver's UNSAT
            // core identifies them as irrelevant to consecution. Previously
            // only the CTG-retry path used core reduction; the base success
            // path took only the one removed literal, which produced
            // cube_len==mic_len on cal14 (frame=2 starts at 73 and stayed at
            // 73 because every single-literal drop looked essential to
            // z4-sat, even though a group drop would have succeeded).
            let core_result = if let Some(ref mut ds) = domain_solver {
                self.is_inductive_with_core_on_solver(ds.as_mut(), &candidate)
            } else {
                self.is_inductive_with_core(frame, &candidate)
            };
            drop_calls += 1;
            if let Some(core_reduced) = core_result {
                // Successful drop (inductive). Apply UNSAT-core reduction to
                // potentially shrink further. `is_inductive_with_core_*`
                // already enforces init-consistency and falls back to the
                // full candidate when the reduction would subsume init.
                // The returned cube is a (possibly strict) subset of
                // `candidate`, so `result.len()` never grows.
                debug_assert!(!core_reduced.is_empty());
                result = core_reduced;
                // Core reduction may have removed literals at positions
                // < i; clamp the loop cursor so the next `i -= 1` stays
                // in bounds. We re-examine the tail regardless since the
                // generalization order is preserved by filter-in-order.
                i = i.min(result.len());
                // Reset consecutive failure counter on success (IC3ref pattern).
                consecutive_failures = 0;
            } else if frame > 1 && self.ctg_recursion_depth < super::engine::MAX_CTG_RECURSION {
                // #4288 TL1f: Gate the CTG inner loop on recursion depth.
                // When depth >= MAX_CTG_RECURSION, fall through to the
                // "essential literal" branch below (matches rIC3's
                // `down()` path at parameter.level=0).
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
                                // SOUNDNESS FIX (#4247): trivial_block can call
                                // add_lemma which performs backward subsumption,
                                // shrinking a frame below its snapshot count.
                                // Clamp old_count to current len to avoid panic.
                                let cur_len = self.frames.frames[f_idx].lemmas.len();
                                let start = old_count.min(cur_len);
                                for lemma in &self.frames.frames[f_idx].lemmas[start..] {
                                    if lemma.lits.iter().any(|l| domain_set.contains(l.var())) {
                                        ds.add_clause(&lemma.lits);
                                    }
                                }
                            }
                        }
                        let inf_start = inf_count.min(self.inf_lemmas.len());
                        for lemma in &self.inf_lemmas[inf_start..] {
                            if lemma.lits.iter().any(|l| domain_set.contains(l.var())) {
                                ds.add_clause(&lemma.lits);
                            }
                        }
                    }
                    // After CTG success, use UNSAT core reduction (#4244).
                    // IC3ref's ctgDown uses the UNSAT core to reduce the cube
                    // directly (IC3.cpp:530-533, 543-546). Extract the core
                    // from the retry check to tighten the result.
                    let retry_core = if let Some(ref mut ds) = domain_solver {
                        self.is_inductive_with_core_on_solver(ds.as_mut(), &candidate)
                    } else {
                        self.is_inductive_with_core(frame, &candidate)
                    };
                    drop_calls += 1;
                    if let Some(core_reduced) = retry_core {
                        // CTG retry succeeded — apply UNSAT core reduction.
                        // Use the tighter core-reduced result if it's valid.
                        if !core_reduced.is_empty()
                            && !self.cube_sat_consistent_with_init(&core_reduced)
                        {
                            result = core_reduced;
                        } else {
                            result = candidate;
                        }
                        dropped = true;
                        // Reset consecutive failure counter.
                        consecutive_failures = 0;
                        // Cap loop index to new result length so the next
                        // `i -= 1` doesn't overflow (result may be shorter
                        // due to core reduction).
                        i = i.min(result.len());
                        break;
                    }
                }
                if !dropped {
                    // Literal is essential — keep it.
                    consecutive_failures += 1;
                }
            } else {
                // Either frame <= 1 (can't recurse further) or
                // ctg_recursion_depth >= MAX_CTG_RECURSION (already inside
                // a recursive CTG call from trivial_block — matches rIC3's
                // `down()` path at parameter.level=0). Literal is essential.
                consecutive_failures += 1;
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
        // #4288: Validate core reduction with independent cross-check before
        // accepting. z4-sat's unsat_core can be unsound (false UNSAT core
        // identifying literals as irrelevant when they aren't), especially
        // on internal-signal-rich cubes. Without validation, the final
        // cross-check at end of MIC will reject the whole generalization
        // and restore the full original cube, wasting Phase 2's work.
        let core_reduced = if let Some(ref mut ds) = domain_solver {
            self.is_inductive_with_core_on_solver(ds.as_mut(), &result)
        } else {
            self.is_inductive_with_core(frame, &result)
        };
        if let Some(core_reduced) = core_reduced {
            if core_reduced.len() < result.len() {
                // Cross-check the reduction for soundness before accepting.
                // Only run cross-check on small circuits (SimpleSolver is too
                // slow on large); on large circuits trust the core.
                let accept = if self.ts.latch_vars.len() <= 60 {
                    self.verify_consecution_independent(frame, &core_reduced, true)
                } else {
                    true
                };
                if accept {
                    result = core_reduced;
                    if domain_solver.is_some() {
                        domain_solver = self.build_mic_domain_solver(frame, &result);
                    }
                }
            }
        }

        // Phase 2: Generalization-order sort + parent lemma heuristic.
        //
        // #4288: Use the FORWARD-iteration sort variant. CTG-down iterates
        // forward (i=0..len) and drops literals from the FRONT first. To
        // mirror rIC3's `mic_by_drop_var` at `ric3/src/ic3/mic.rs:225` —
        // `activity.sort_by_activity(&mut cube, true)` with `ascending=true`
        // — we need low-activity literals at the FRONT so they're tried for
        // removal first. Previously this path used the backward-sort helper
        // (descending), which tried HIGH-activity literals first — the
        // opposite of rIC3's proven heuristic.
        self.sort_for_generalization_forward(&mut result);
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
                let parent_set: rustc_hash::FxHashSet<Lit> = parent_cube.into_iter().collect();
                result.sort_by_key(|lit| parent_set.contains(lit));
            }
        }

        // Phase 3: CTG-down literal dropping with (s,t) cex caching.
        let mut keep = rustc_hash::FxHashSet::default();
        let mut cex_cache: Vec<(Lemma, Lemma)> = Vec::new();
        let budget = self.config.mic_drop_budget;
        let mic_attempts = self.config.mic_attempts;
        let mut drop_calls = 0usize;
        let mut consecutive_failures = 0usize;
        let mut i = 0;
        while i < result.len() {
            if result.len() <= 1 {
                break;
            }
            if budget > 0 && drop_calls >= budget {
                break;
            }
            // Consecutive failure early abort (#4244, IC3ref micAttempts).
            if mic_attempts > 0 && consecutive_failures >= mic_attempts {
                break;
            }
            // Cooperative cancellation (#4096): CTG-down forward iteration can
            // make hundreds of SAT calls. Check cancellation each iteration.
            if self.is_cancelled() {
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
            let cex_hit = cex_cache
                .iter()
                .any(|(s, t)| !candidate_lemma.subsumes(s) && candidate_lemma.subsumes(t));
            if cex_hit {
                keep.insert(result[i]);
                i += 1;
                consecutive_failures += 1;
                continue;
            }

            // #4288: Use UNSAT-core reduction on every successful drop
            // (matches rIC3's mic_by_drop_var + handle_down_success). The
            // core may drop MANY additional literals beyond the one we
            // removed. Forward iteration: after filtering result by core,
            // advance `i` past the already-kept prefix to preserve progress.
            let core_result = if let Some(ref mut ds) = domain_solver {
                self.is_inductive_with_core_on_solver(ds.as_mut(), &candidate)
            } else {
                self.is_inductive_with_core(frame, &candidate)
            };
            drop_calls += 1;
            if let Some(core_reduced) = core_result {
                debug_assert!(!core_reduced.is_empty());
                // Filter result by core in original order (like rIC3
                // handle_down_success) so cursor math makes sense.
                let core_set: rustc_hash::FxHashSet<Lit> = core_reduced.iter().copied().collect();
                let new_result: Vec<Lit> = result
                    .iter()
                    .copied()
                    .filter(|l| core_set.contains(l))
                    .collect();
                debug_assert!(!new_result.is_empty());
                // Advance `i` to first literal not in the already-processed
                // prefix (result[0..i]). This is rIC3's pattern and ensures
                // we don't revisit literals that were already kept/skipped.
                let processed_prefix: rustc_hash::FxHashSet<Lit> =
                    result[..i].iter().copied().collect();
                let new_i = new_result
                    .iter()
                    .position(|l| !processed_prefix.contains(l))
                    .unwrap_or(new_result.len());
                result = new_result;
                i = new_i;
                // Reset consecutive failure counter on success.
                consecutive_failures = 0;
                continue;
            }

            // Drop failed — attempt CTG-down shrinking.
            // #4288 TL1f: Gate CTG-down shrinking on recursion depth. When
            // already inside a recursive CTG (trivial_block → mic → here),
            // fall back to the "essential literal" path below to mirror
            // rIC3's `parameter.level=0` behavior (no further CTG).
            if frame > 1 && self.ctg_recursion_depth < super::engine::MAX_CTG_RECURSION {
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

                    if ctg_count < self.config.ctg_max && !self.cube_consistent_with_init(&pred) {
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
                                        // SOUNDNESS FIX (#4247): trivial_block can
                                        // call add_lemma which performs backward
                                        // subsumption, shrinking a frame below its
                                        // snapshot count. Clamp to avoid panic.
                                        let cur_len = self.frames.frames[f_idx].lemmas.len();
                                        let start = old_count.min(cur_len);
                                        for lemma in &self.frames.frames[f_idx].lemmas[start..] {
                                            if lemma
                                                .lits
                                                .iter()
                                                .any(|l| domain_set.contains(l.var()))
                                            {
                                                ds.add_clause(&lemma.lits);
                                            }
                                        }
                                    }
                                }
                                let inf_start = inf_count.min(self.inf_lemmas.len());
                                for lemma in &self.inf_lemmas[inf_start..] {
                                    if lemma.lits.iter().any(|l| domain_set.contains(l.var())) {
                                        ds.add_clause(&lemma.lits);
                                    }
                                }
                            }
                            // After CTG success, use UNSAT core reduction (#4244).
                            let retry_core = if let Some(ref mut ds) = domain_solver {
                                self.is_inductive_with_core_on_solver(ds.as_mut(), &candidate)
                            } else {
                                self.is_inductive_with_core(frame, &candidate)
                            };
                            if let Some(core_reduced) = retry_core {
                                if !core_reduced.is_empty()
                                    && !self.cube_sat_consistent_with_init(&core_reduced)
                                {
                                    result = core_reduced;
                                } else {
                                    result = candidate;
                                }
                                shrunk = true;
                                // Reset i=0: core reduction may produce a shorter
                                // result, so restart forward iteration from the
                                // beginning to re-check all remaining literals.
                                i = 0;
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
                        .filter(|&&lit| model_solver.value(lit).unwrap_or(false))
                        .copied()
                        .collect();

                    let use_flip = self.config.flip_to_none_lift;

                    // Cache (s,t) counterexample pair.
                    {
                        let s_lits: Vec<Lit> = if use_flip {
                            self.ts
                                .latch_vars
                                .iter()
                                .filter_map(|&lv| {
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
                                })
                                .collect()
                        } else {
                            self.ts
                                .latch_vars
                                .iter()
                                .filter_map(|&lv| {
                                    model_solver.value(Lit::pos(lv)).map(|val| {
                                        if val {
                                            Lit::pos(lv)
                                        } else {
                                            Lit::neg(lv)
                                        }
                                    })
                                })
                                .collect()
                        };
                        let t_lits: Vec<Lit> = self
                            .ts
                            .latch_vars
                            .iter()
                            .filter_map(|&lv| {
                                if let Some(&next_var) = self.next_vars.get(&lv) {
                                    model_solver.value(Lit::pos(next_var)).map(|val| {
                                        if val {
                                            Lit::pos(lv)
                                        } else {
                                            Lit::neg(lv)
                                        }
                                    })
                                } else {
                                    None
                                }
                            })
                            .collect();
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
                    consecutive_failures += 1;
                } else {
                    // Reset consecutive failure counter on successful shrink.
                    consecutive_failures = 0;
                }
            } else {
                keep.insert(result[i]);
                i += 1;
                consecutive_failures += 1;
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
    pub(super) fn trivial_block(
        &mut self,
        frame: usize,
        cube: Vec<Lit>,
        limit: &mut usize,
    ) -> bool {
        if frame == 0 || *limit == 0 {
            return false;
        }
        // Cooperative cancellation (#4096): trivial_block recurses through
        // predecessors and each level makes SAT calls. Check cancellation
        // at each recursion entry to exit promptly.
        if self.is_cancelled() {
            return false;
        }
        if self.cube_sat_consistent_with_init(&cube) {
            return false;
        }
        *limit -= 1;
        loop {
            if self.is_inductive(frame, &cube) {
                // #4288 TL1f: Recursive CTG generalization.
                //
                // rIC3's `trivial_block_rec` calls `mic()` with
                // `MicType::DropVar(parameter.sub_level())` — meaning the
                // inner MIC can do ONE MORE level of CTG if the outer is at
                // level>=1, otherwise falls back to plain `down()`. See
                // rIC3 `ic3/block.rs:209-213` and `ic3/mic.rs:202-272`.
                //
                // We mirror this with `ctg_recursion_depth`: the outermost
                // MIC call runs at depth 0 (full CTG enabled), and any
                // recursion into `trivial_block` raises depth to 1 (which
                // disables the CTG inner loop in `mic()` / `mic_ctg_down()`,
                // mimicking rIC3's `down()` path). Bounded at
                // `MAX_CTG_RECURSION` to prevent exponential blowup.
                //
                // On clause-heavy UNSAT benchmarks like cal14 (23 latches,
                // 1656 trans clauses), the previous `mic_simple` call
                // produced under-generalized predecessor lemmas that failed
                // to strengthen the frame enough to unstick the outer MIC.
                // One level of recursive CTG gives the inner MIC a chance
                // to drop more literals, producing tighter frame lemmas
                // that help the outer cube's generalization converge.
                let generalized = if self.ctg_recursion_depth < super::engine::MAX_CTG_RECURSION {
                    self.ctg_recursion_depth += 1;
                    let r = self.mic(frame, cube);
                    self.ctg_recursion_depth -= 1;
                    r
                } else {
                    self.mic_simple(frame, cube)
                };
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
                if lemma_idx > 0 {
                    self.earliest_changed_frame = self.earliest_changed_frame.min(lemma_idx);
                }
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

        // #4288: Apply activity-guided literal ordering before the drop loop,
        // matching the primary `mic()` path and rIC3's `mic_by_drop_var` at
        // `ric3/src/ic3/mic.rs:225`. `mic_simple` uses BACKWARD iteration
        // (while i > 0 { i -= 1 }), so descending sort (high activity at front)
        // means low-activity literals at the END are tried for removal FIRST.
        // Previously `mic_simple` used the cube's arbitrary incoming order —
        // missing the drop-order heuristic that makes MIC shrinkage effective.
        self.sort_for_generalization(&mut result);

        let budget = self.config.mic_drop_budget;
        let mic_attempts = self.config.mic_attempts;
        let mut drop_calls = 0usize;
        let mut consecutive_failures = 0usize;
        let mut i = result.len();
        while i > 0 {
            i -= 1;
            if result.len() <= 1 {
                break;
            }
            if budget > 0 && drop_calls >= budget {
                break;
            }
            // Consecutive failure early abort (#4244, IC3ref micAttempts).
            if mic_attempts > 0 && consecutive_failures >= mic_attempts {
                break;
            }
            // Cooperative cancellation (#4096).
            if self.is_cancelled() {
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
                consecutive_failures = 0;
            } else {
                consecutive_failures += 1;
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
        // #4288: Bump activity on the surviving cube (matches rIC3
        // `mic_by_drop_var` at `ric3/src/ic3/mic.rs:269` —
        // `self.activity.bump_cube_activity(&cube)` after MIC completes).
        // Previously `mic_simple` did not bump, so activity feedback was
        // lost for the recursive-CTG-fallback path.
        self.bump_activity(&result);
        self.decay_activity();
        result
    }

    /// Check if a cube is inductive relative to frame[frame-1] with !cube strengthening.
    ///
    /// When the circuit has >= 20 latches, uses z4-sat's native domain restriction
    /// (`set_domain`/`clear_domain`) on the frame solver to restrict BCP and VSIDS
    /// branching to the cube's cone-of-influence variables. This is the same
    /// optimization applied in `block_one`, `push_lemma`, and `propagation_blocked`,
    /// now extended to the `trivial_block` path where `is_inductive` is called
    /// repeatedly without a dedicated domain-restricted mini-solver.
    ///
    /// Note: MIC callers that use `is_inductive_on_solver` already have a
    /// clause-filtered mini-solver with `set_domain` wired in by
    /// `build_domain_restricted_solver`. This method adds native domain BCP
    /// only for the frame solver path (trivial_block, push_lemma pre-check).
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

        // Activate z4-sat native domain restriction for this query.
        // Near-zero setup cost: just sets a bitvec in z4-sat. Significant
        // per-call benefit: domain-restricted BCP skips non-domain watchers,
        // and VSIDS only branches on domain variables.
        let use_domain = self.ts.latch_vars.len() >= 20;
        if use_domain {
            let domain = self.domain_computer.compute_domain(cube, &self.next_vars);
            let domain_vars: Vec<Var> = (0..=self.max_var)
                .filter(|&i| domain.contains(Var(i)))
                .map(Var)
                .collect();
            self.solvers[solver_idx].set_domain(&domain_vars);
        }

        let result = self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube)
            == SatResult::Unsat;

        if use_domain {
            self.solvers[solver_idx].clear_domain();
        }

        result
    }

    /// TL1d (#4288): Given a cube whose core-derived latches-only subset is
    /// init-consistent, find a small subset of internal-signal literals from
    /// the cube such that (core_latches ∪ subset) is init-inconsistent.
    ///
    /// Bisection search: start with all internal signals from the cube; if
    /// removing the first half keeps init-inconsistency, recurse on the
    /// second half, and vice versa. Produces an O(log n) subset in the
    /// worst case.
    ///
    /// Returns `Vec::new()` if no such subset exists (cube is genuinely
    /// init-consistent even with all signals included — should be impossible
    /// since the caller verified original cube is init-inconsistent).
    pub(super) fn bisect_internal_signals_for_init(
        &self,
        cube: &[Lit],
        core_latch_vars: &rustc_hash::FxHashSet<Var>,
    ) -> Vec<Lit> {
        // Partition cube into latch subset (always kept) and signal lits
        // (candidates for pruning).
        let mut latch_part: Vec<Lit> = Vec::new();
        let mut signal_part: Vec<Lit> = Vec::new();
        for &lit in cube {
            if core_latch_vars.contains(&lit.var()) {
                latch_part.push(lit);
            } else if !self.reverse_next.contains_key(&lit.var())
                && !self.next_vars.contains_key(&lit.var())
            {
                // Non-latch var with no next mapping — this is an internal
                // signal (or input); treat as prunable. Latch vars (in
                // next_vars) that aren't in core_latch_vars are dropped
                // anyway per the caller's filter logic.
                signal_part.push(lit);
            }
        }
        if signal_part.is_empty() {
            return Vec::new();
        }
        // Check: with all signals, cube is init-inconsistent (required
        // precondition). With no signals (latch_part only), caller proved
        // it's init-consistent. Bisect signal_part.
        let full_check = {
            let mut full = latch_part.clone();
            full.extend(&signal_part);
            self.cube_sat_consistent_with_init(&full)
        };
        if full_check {
            // Precondition violated: full cube IS init-consistent. Caller
            // shouldn't invoke us in this case; bail to fallback.
            return Vec::new();
        }
        // Linear shrink: drop one signal at a time if cube remains
        // init-inconsistent. Simpler than bisection, and since typical
        // cal14 cubes have ~50 signals and each check is fast (no SAT
        // call — uses cube_sat_consistent_with_init which bitmasks init),
        // O(n) total probes is acceptable.
        //
        // Note: cube_sat_consistent_with_init DOES call SAT when init has
        // non-unit clauses; linear drop would do 50 SAT calls. But cal14
        // has 23 unit init clauses (all-zero), so the fast path applies
        // and each check is O(|cube|) bitwise.
        let mut current = signal_part;
        let mut i = current.len();
        while i > 0 {
            i -= 1;
            let candidate: Vec<Lit> = current
                .iter()
                .enumerate()
                .filter_map(|(j, &l)| if j != i { Some(l) } else { None })
                .collect();
            let mut probe = latch_part.clone();
            probe.extend(&candidate);
            if !self.cube_sat_consistent_with_init(&probe) {
                current = candidate;
            }
        }
        // Stitch back: latch_part (in original cube order) + surviving signals.
        // To preserve cube order, iterate cube and keep items from either set.
        let signal_set: rustc_hash::FxHashSet<Lit> = current.iter().copied().collect();
        cube.iter()
            .filter(|l| core_latch_vars.contains(&l.var()) || signal_set.contains(l))
            .copied()
            .collect()
    }

    /// Check inductiveness and return the UNSAT core-reduced cube if inductive.
    ///
    /// Uses z4-sat native domain restriction on circuits with >= 20 latches,
    /// matching the pattern in `is_inductive`.
    pub(super) fn is_inductive_with_core(
        &mut self,
        frame: usize,
        cube: &[Lit],
    ) -> Option<Vec<Lit>> {
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

        // Activate z4-sat native domain restriction for this query.
        let use_domain = self.ts.latch_vars.len() >= 20;
        if use_domain {
            let domain = self.domain_computer.compute_domain(cube, &self.next_vars);
            let domain_vars: Vec<Var> = (0..=self.max_var)
                .filter(|&i| domain.contains(Var(i)))
                .map(Var)
                .collect();
            self.solvers[solver_idx].set_domain(&domain_vars);
        }

        let result = self.solvers[solver_idx].solve_with_temporary_clause(&assumptions, &neg_cube);

        if use_domain {
            self.solvers[solver_idx].clear_domain();
        }

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
        //
        // #4288: rIC3-style init-disjoint repair (gipsat/ts.rs:77). See
        // is_inductive_with_core_on_solver for details.
        if self.cube_sat_consistent_with_init(&reduced) {
            // TL1d (#4288): Internal-signal bisection repair. See
            // is_inductive_with_core_on_solver for rationale.
            let ans_bisect = self.bisect_internal_signals_for_init(cube, &core_latch_vars);
            if !ans_bisect.is_empty() && ans_bisect.len() < cube.len() {
                return Some(ans_bisect);
            }
            let init_map = &self.init_map;
            let extra: Option<Lit> = cube
                .iter()
                .find(|lit| {
                    init_map
                        .get(&lit.var())
                        .is_some_and(|&init_pol| lit.is_positive() != init_pol)
                })
                .copied();
            if let Some(extra_lit) = extra {
                let mut ans: Vec<Lit> = cube
                    .iter()
                    .filter(|lit| core_latch_vars.contains(&lit.var()) || **lit == extra_lit)
                    .copied()
                    .collect();
                if !self.cube_consistent_with_init(&ans) {
                    ans.sort_by_key(|l| l.var().0);
                    ans.dedup();
                    if !ans.is_empty() && ans.len() < cube.len() {
                        return Some(ans);
                    }
                }
            }
            Some(cube.to_vec())
        } else {
            Some(reduced)
        }
    }

    /// Check inductiveness using a domain-restricted solver.
    pub(super) fn is_inductive_on_solver(&self, solver: &mut dyn SatSolver, cube: &[Lit]) -> bool {
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
        if std::env::var("IC3_CORE_DEBUG").is_ok() {
            eprintln!(
                "CORE: cube_len={} core_lits={} reduced={}",
                cube.len(),
                core.len(),
                reduced.len(),
            );
        }
        if reduced.is_empty() {
            return Some(cube.to_vec());
        }
        // SOUNDNESS FIX (#4092): Use precise SAT-based init check.
        //
        // #4288: Tiered fallback for internal-signal cubes. When the core
        // returns latches only but the latches-only subset is init-consistent,
        // progressively add back internal signals from the original cube
        // rather than falling back to the full 73-lit cube. This is essential
        // on cal14 where the cube has 23 latches (all init-consistent when
        // init=all-zeros) + 50 internal signals. Internal signals are dropped
        // from the core-extracted latch filter because they have no
        // next_vars mapping — but they ARE needed to make the cube
        // init-inconsistent. Re-adding them keeps correctness while
        // potentially dropping MANY latches.
        if self.cube_sat_consistent_with_init(&reduced) {
            // TL1d (#4288): Internal-signal bisection repair. When the
            // latches-only reduction is init-consistent but the FULL cube is
            // init-inconsistent, the init-distinguishing information lives in
            // the internal signals (not the latches, not init_map).
            // Rather than falling back to the full 53-lit cube, bisect the
            // cube's internal-signal portion: try half, then check
            // init-consistency. This produces latches + O(log n) signals
            // rather than latches + ALL n signals.
            let mut ans = self.bisect_internal_signals_for_init(cube, &core_latch_vars);
            if !ans.is_empty() && ans.len() < cube.len() {
                return Some(ans);
            }
            ans.clear(); // drop allocation
                         // #4288: rIC3-style init-disjoint repair (gipsat/ts.rs:77).
                         // When the core-reduced cube is init-consistent, add back the
                         // FIRST literal from the original cube whose polarity contradicts
                         // init. This makes the cube init-inconsistent with minimal
                         // overhead (+1 literal) rather than falling back to the full cube.
                         //
                         // Iteration order: preserve the original cube's ordering so the
                         // "first init-contradicting" choice is deterministic and repeatable.
            let init_map = &self.init_map;
            let extra: Option<Lit> = cube
                .iter()
                .find(|lit| {
                    init_map
                        .get(&lit.var())
                        .is_some_and(|&init_pol| lit.is_positive() != init_pol)
                })
                .copied();
            if let Some(extra_lit) = extra {
                // Rebuild: core lits + the init-contradicting lit (if not
                // already present), preserving cube order.
                let mut ans: Vec<Lit> = cube
                    .iter()
                    .filter(|lit| core_latch_vars.contains(&lit.var()) || **lit == extra_lit)
                    .copied()
                    .collect();
                // Defense: confirm init-inconsistent (since extra_lit
                // contradicts init_map, the fast path guarantees this).
                if !self.cube_consistent_with_init(&ans) {
                    // Deduplicate (extra_lit may already have been in core).
                    ans.sort_by_key(|l| l.var().0);
                    ans.dedup();
                    if !ans.is_empty() && ans.len() < cube.len() {
                        return Some(ans);
                    }
                }
            }
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
        let domain = self.domain_computer.compute_domain(cube, &self.next_vars);

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
    ) -> Option<(Box<dyn SatSolver>, domain::DomainSet)> {
        if self.ts.latch_vars.len() < 20 {
            return None;
        }

        let domain = self.domain_computer.compute_domain(cube, &self.next_vars);

        let solver = domain::build_domain_restricted_solver(
            &domain,
            &self.ts,
            &self.next_link_clauses,
            &self.frames.frames,
            frame.saturating_sub(1),
            &self.inf_lemmas,
            self.solver_backend,
            self.max_var,
        )?;
        Some((solver, domain))
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
        self.consecution_stats.log_summary();
    }
}

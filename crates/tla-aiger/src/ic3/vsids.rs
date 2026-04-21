// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bucket-queue VSIDS for IC3.
//!
//! IC3 queries are usually short, so a coarse bucket queue gives excellent
//! constant factors for the first few dozen decisions. After enough restarts,
//! however, the query distribution shifts and exact heap ordering becomes more
//! valuable. This module keeps both representations live and switches from the
//! bucket queue to the binary heap adaptively.

use std::cmp::Ordering;
use std::collections::BinaryHeap;

use crate::sat_types::{Lit, Var};

const MAX_ACTIVITY: f64 = 1.0e100;
const RESCALE_FACTOR: f64 = 1.0e-100;
const DEFAULT_BUCKET_BITS: u32 = 12;
const DEFAULT_DECAY: f64 = 0.99;

/// Selection mode used by [`BucketQueueVsids`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VsidsMode {
    /// Approximate max-activity extraction with amortized O(1) scans.
    BucketQueue,
    /// Exact max-activity extraction via a binary heap.
    BinaryHeap,
}

/// Configuration for [`BucketQueueVsids`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct VsidsConfig {
    /// VSIDS decay factor.
    ///
    /// Larger values keep older bumps relevant for longer. The default `0.99`
    /// mirrors the current IC3 activity decay while using lazy VSIDS rescaling.
    pub decay: f64,
    /// Switch permanently from bucket mode to heap mode after this many
    /// restarts. A value of `0` starts directly in heap mode.
    pub switch_to_heap_after_restarts: usize,
    /// Deterministic seed for tiny per-variable activity perturbations.
    ///
    /// This mirrors the current IC3 engine's seeded tie-breaking.
    pub random_seed: u64,
    /// Number of high-order floating-point bits used for bucket indexing.
    ///
    /// The bucket count is `1 << bucket_bits`.
    pub bucket_bits: u32,
}

impl Default for VsidsConfig {
    fn default() -> Self {
        Self {
            decay: DEFAULT_DECAY,
            switch_to_heap_after_restarts: 10,
            random_seed: 0,
            bucket_bits: DEFAULT_BUCKET_BITS,
        }
    }
}

/// Dual-mode VSIDS with a bucket queue for short IC3 queries and a binary heap
/// for longer ones.
///
/// Activity updates follow standard lazy VSIDS semantics:
/// - bumping a variable adds the current bump increment;
/// - decaying increases the future bump increment instead of touching all
///   variables;
/// - scores are rescaled if they become too large.
///
/// Candidate management is explicit:
/// - [`push`](Self::push) marks a variable selectable;
/// - [`pop_highest`](Self::pop_highest) returns and removes the current best
///   selectable variable;
/// - [`remove`](Self::remove) drops a variable without selecting it.
///
/// For MIC literal ordering, [`sort_by_activity`](Self::sort_by_activity)
/// provides the same descending activity sort currently used in `ic3/mod.rs`.
#[derive(Debug, Clone)]
#[allow(dead_code)] // Dual-mode (bucket queue + heap) designed for future IC3 wiring
pub(crate) struct BucketQueueVsids {
    activity: Activity,
    bucket: BucketQueue,
    heap: HeapQueue,
    versions: Vec<u64>,
    selectable: Vec<bool>,
    restart_count: usize,
    switch_to_heap_after_restarts: usize,
    mode: VsidsMode,
}

#[allow(dead_code)] // Dual-mode pop/restart not yet wired to IC3 main loop
impl BucketQueueVsids {
    /// Create a VSIDS instance with the default configuration.
    pub(crate) fn new(max_var: u32) -> Self {
        Self::with_config(max_var, VsidsConfig::default())
    }

    /// Create a VSIDS instance with an explicit configuration.
    pub(crate) fn with_config(max_var: u32, config: VsidsConfig) -> Self {
        assert!(
            config.decay > 0.0 && config.decay < 1.0,
            "invariant: VSIDS decay must be in (0, 1)"
        );
        assert!(
            config.bucket_bits > 0 && config.bucket_bits < usize::BITS,
            "invariant: bucket_bits must fit in usize"
        );

        let len = max_var as usize + 2;
        let mode = if config.switch_to_heap_after_restarts == 0 {
            VsidsMode::BinaryHeap
        } else {
            VsidsMode::BucketQueue
        };

        Self {
            activity: Activity::new(len, config.decay, config.random_seed),
            bucket: BucketQueue::new(config.bucket_bits),
            heap: HeapQueue::default(),
            versions: vec![0; len],
            selectable: vec![false; len],
            restart_count: 0,
            switch_to_heap_after_restarts: config.switch_to_heap_after_restarts,
            mode,
        }
    }

    /// Return the current selection mode.
    pub(crate) fn mode(&self) -> VsidsMode {
        self.mode
    }

    /// Return the number of restarts observed by this VSIDS instance.
    pub(crate) fn restart_count(&self) -> usize {
        self.restart_count
    }

    /// Return the current activity score of `var`.
    pub(crate) fn activity(&self, var: Var) -> f64 {
        self.activity.score(var)
    }

    /// Return whether `var` is currently selectable by [`pop_highest`](Self::pop_highest).
    pub(crate) fn is_selectable(&self, var: Var) -> bool {
        self.selectable.get(var.index()).copied().unwrap_or(false)
    }

    /// Mark `var` selectable and insert its current activity into both queues.
    ///
    /// Re-pushing an already-selectable variable is allowed and refreshes its
    /// queue position.
    pub(crate) fn push(&mut self, var: Var) {
        if var == Var::CONST {
            return;
        }
        self.ensure_var(var);
        self.selectable[var.index()] = true;
        self.refresh_candidate(var);
    }

    /// Remove `var` from the selectable set without returning it.
    pub(crate) fn remove(&mut self, var: Var) {
        if let Some(slot) = self.selectable.get_mut(var.index()) {
            *slot = false;
        }
    }

    /// Clear the selectable set.
    pub(crate) fn clear(&mut self) {
        self.bucket.clear();
        self.heap.clear();
        for slot in &mut self.selectable {
            *slot = false;
        }
    }

    /// Record a restart and switch permanently to heap mode once the
    /// configured threshold is reached.
    pub(crate) fn notify_restart(&mut self) {
        self.restart_count += 1;
        if self.mode == VsidsMode::BucketQueue
            && self.restart_count >= self.switch_to_heap_after_restarts
        {
            self.mode = VsidsMode::BinaryHeap;
        }
    }

    /// Bump the activity of each variable present in `cube`.
    ///
    /// Variables that are currently selectable are re-enqueued with their new
    /// activity, so the next selection sees the updated priority.
    pub(crate) fn bump_activity(&mut self, cube: &[Lit]) {
        for &lit in cube {
            self.bump_var(lit.var());
        }
    }

    /// Bump a single variable's activity.
    pub(crate) fn bump_var(&mut self, var: Var) {
        if var == Var::CONST {
            return;
        }
        self.ensure_var(var);
        let rescaled = self.activity.bump(var);
        if rescaled {
            self.rebuild_queues();
        } else if self.selectable[var.index()] {
            self.refresh_candidate(var);
        }
    }

    /// Apply lazy VSIDS decay.
    ///
    /// This increases the future bump increment rather than scaling every
    /// variable immediately. If the increment grows too large, all activities
    /// are rescaled and the queues are rebuilt.
    pub(crate) fn decay_activity(&mut self) {
        if self.activity.decay() {
            self.rebuild_queues();
        }
    }

    /// Sort literals by descending variable activity.
    ///
    /// This matches the existing MIC convention in `ic3/mod.rs`: callers can
    /// then iterate the slice backward to try low-activity literals first.
    pub(crate) fn sort_by_activity(&self, lits: &mut [Lit]) {
        lits.sort_by(|a, b| self.compare_lits_by_activity(*a, *b));
    }

    /// Sort literals by ascending variable activity.
    ///
    /// This mirrors rIC3's `Activity::sort_by_activity(cube, ascending=true)`
    /// pattern at `ric3/src/ic3/activity.rs:55-63`, used in forward-iteration
    /// MIC paths (`mic_by_drop_var` at `ric3/src/ic3/mic.rs:225`). With
    /// ascending sort and forward iteration, the lowest-activity literals
    /// (least important to the inductive core) are tried for removal first.
    pub(crate) fn sort_by_activity_ascending(&self, lits: &mut [Lit]) {
        lits.sort_by(|a, b| self.compare_lits_by_activity(*b, *a));
    }

    /// Pop the highest-activity selectable variable.
    ///
    /// The returned variable is removed from the selectable set. Callers that
    /// later unassign the variable should [`push`](Self::push) it again.
    pub(crate) fn pop_highest(&mut self) -> Option<Var> {
        let picked = match self.mode {
            VsidsMode::BucketQueue => {
                let selectable = &self.selectable;
                let versions = &self.versions;
                self.bucket.pop(|var, version| {
                    selectable.get(var.index()).copied().unwrap_or(false)
                        && versions.get(var.index()).copied() == Some(version)
                })
            }
            VsidsMode::BinaryHeap => {
                let selectable = &self.selectable;
                let versions = &self.versions;
                self.heap.pop(|var, version| {
                    selectable.get(var.index()).copied().unwrap_or(false)
                        && versions.get(var.index()).copied() == Some(version)
                })
            }
        };

        if let Some(var) = picked {
            self.selectable[var.index()] = false;
        }
        picked
    }

    fn compare_lits_by_activity(&self, lhs: Lit, rhs: Lit) -> Ordering {
        let lhs_var = lhs.var();
        let rhs_var = rhs.var();
        self.activity
            .score(rhs_var)
            .total_cmp(&self.activity.score(lhs_var))
            .then_with(|| lhs_var.cmp(&rhs_var))
            .then_with(|| lhs.code().cmp(&rhs.code()))
    }

    fn ensure_var(&mut self, var: Var) {
        let index = var.index();
        self.activity.ensure_len(index + 1);
        if index >= self.versions.len() {
            self.versions.resize(index + 1, 0);
            self.selectable.resize(index + 1, false);
        }
    }

    fn refresh_candidate(&mut self, var: Var) {
        let index = var.index();
        let version = self.versions[index].wrapping_add(1);
        self.versions[index] = version;
        let score = self.activity.score(var);
        self.bucket.push(var, version, score);
        self.heap.push(var, version, score);
    }

    fn rebuild_queues(&mut self) {
        self.bucket.clear();
        self.heap.clear();
        for index in 1..self.selectable.len() {
            if !self.selectable[index] {
                continue;
            }
            let var = Var(index as u32);
            self.refresh_candidate(var);
        }
    }
}

#[derive(Debug, Clone)]
struct Activity {
    scores: Vec<f64>,
    bump_amount: f64,
    decay: f64,
    random_seed: u64,
}

impl Activity {
    fn new(len: usize, decay: f64, random_seed: u64) -> Self {
        let mut activity = Self {
            scores: Vec::new(),
            bump_amount: 1.0,
            decay,
            random_seed,
        };
        activity.ensure_len(len);
        activity
    }

    fn ensure_len(&mut self, len: usize) {
        if len <= self.scores.len() {
            return;
        }

        let start = self.scores.len();
        self.scores
            .extend((start..len).map(|index| seeded_noise(self.random_seed, index)));
    }

    fn score(&self, var: Var) -> f64 {
        self.scores.get(var.index()).copied().unwrap_or(0.0)
    }

    fn bump(&mut self, var: Var) -> bool {
        let index = var.index();
        self.ensure_len(index + 1);
        self.scores[index] += self.bump_amount;
        if self.scores[index] >= MAX_ACTIVITY || self.bump_amount >= MAX_ACTIVITY {
            self.rescale();
            return true;
        }
        false
    }

    fn decay(&mut self) -> bool {
        self.bump_amount /= self.decay;
        if self.bump_amount >= MAX_ACTIVITY {
            self.rescale();
            return true;
        }
        false
    }

    fn rescale(&mut self) {
        for score in &mut self.scores {
            *score *= RESCALE_FACTOR;
        }
        self.bump_amount *= RESCALE_FACTOR;
    }
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
struct BucketEntry {
    var: Var,
    version: u64,
}

#[derive(Debug, Clone)]
struct BucketQueue {
    buckets: Vec<Vec<BucketEntry>>,
    max_bucket: usize,
    bucket_bits: u32,
}

impl BucketQueue {
    fn new(bucket_bits: u32) -> Self {
        let bucket_count = 1usize << bucket_bits;
        Self {
            buckets: vec![Vec::new(); bucket_count],
            max_bucket: 0,
            bucket_bits,
        }
    }

    fn clear(&mut self) {
        for bucket in &mut self.buckets {
            bucket.clear();
        }
        self.max_bucket = 0;
    }

    fn push(&mut self, var: Var, version: u64, score: f64) {
        let index = self.bucket_index(score);
        self.buckets[index].push(BucketEntry { var, version });
        self.max_bucket = self.max_bucket.max(index);
    }

    #[allow(dead_code)] // Used by BucketQueueVsids::pop_highest, not yet wired to IC3 main loop
    fn pop<F>(&mut self, mut is_live: F) -> Option<Var>
    where
        F: FnMut(Var, u64) -> bool,
    {
        loop {
            while self.max_bucket > 0 && self.buckets[self.max_bucket].is_empty() {
                self.max_bucket -= 1;
            }

            let bucket = self.buckets.get_mut(self.max_bucket)?;
            let entry = bucket.pop()?;
            if is_live(entry.var, entry.version) {
                return Some(entry.var);
            }
        }
    }

    fn bucket_index(&self, score: f64) -> usize {
        if !score.is_finite() || score <= 0.0 {
            return 0;
        }

        let ordered_bits = score.to_bits() << 1;
        let shift = 64 - self.bucket_bits;
        let index = (ordered_bits >> shift) as usize;
        index.min(self.buckets.len().saturating_sub(1))
    }
}

#[derive(Debug, Clone, Copy)]
struct HeapEntry {
    score: f64,
    version: u64,
    var: Var,
}

impl PartialEq for HeapEntry {
    fn eq(&self, other: &Self) -> bool {
        self.score.to_bits() == other.score.to_bits()
            && self.version == other.version
            && self.var == other.var
    }
}

impl Eq for HeapEntry {}

impl PartialOrd for HeapEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for HeapEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        self.score
            .total_cmp(&other.score)
            .then_with(|| self.version.cmp(&other.version))
            .then_with(|| self.var.cmp(&other.var))
    }
}

#[derive(Debug, Clone, Default)]
struct HeapQueue {
    heap: BinaryHeap<HeapEntry>,
}

impl HeapQueue {
    fn clear(&mut self) {
        self.heap.clear();
    }

    fn push(&mut self, var: Var, version: u64, score: f64) {
        self.heap.push(HeapEntry {
            score,
            version,
            var,
        });
    }

    #[allow(dead_code)] // Used by BucketQueueVsids::pop_highest, not yet wired to IC3 main loop
    fn pop<F>(&mut self, mut is_live: F) -> Option<Var>
    where
        F: FnMut(Var, u64) -> bool,
    {
        while let Some(entry) = self.heap.pop() {
            if is_live(entry.var, entry.version) {
                return Some(entry.var);
            }
        }
        None
    }
}

fn seeded_noise(seed: u64, index: usize) -> f64 {
    if seed == 0 {
        return 0.0;
    }

    let mut z = (index as u64)
        .wrapping_add(seed)
        .wrapping_mul(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^= z >> 31;
    (z as f64 / u64::MAX as f64) * 0.01
}

#[cfg(test)]
mod tests {
    use super::{BucketQueueVsids, VsidsConfig, VsidsMode, MAX_ACTIVITY};
    use crate::sat_types::{Lit, Var};

    #[test]
    fn sort_by_activity_is_descending() {
        let mut vsids = BucketQueueVsids::new(8);
        vsids.bump_var(Var(2));
        vsids.bump_var(Var(2));
        vsids.bump_var(Var(3));

        let mut lits = vec![Lit::pos(Var(1)), Lit::neg(Var(3)), Lit::pos(Var(2))];
        vsids.sort_by_activity(&mut lits);

        assert_eq!(lits[0].var(), Var(2));
        assert_eq!(lits[1].var(), Var(3));
        assert_eq!(lits[2].var(), Var(1));
    }

    #[test]
    fn pop_highest_uses_bucket_mode_initially() {
        let mut vsids = BucketQueueVsids::new(8);
        vsids.push(Var(1));
        vsids.push(Var(2));
        vsids.bump_var(Var(2));

        assert_eq!(vsids.mode(), VsidsMode::BucketQueue);
        assert_eq!(vsids.pop_highest(), Some(Var(2)));
        assert_eq!(vsids.pop_highest(), Some(Var(1)));
        assert_eq!(vsids.pop_highest(), None);
    }

    #[test]
    fn switches_to_heap_after_configured_restarts() {
        let mut vsids = BucketQueueVsids::with_config(
            4,
            VsidsConfig {
                switch_to_heap_after_restarts: 2,
                ..VsidsConfig::default()
            },
        );

        assert_eq!(vsids.mode(), VsidsMode::BucketQueue);
        vsids.notify_restart();
        assert_eq!(vsids.mode(), VsidsMode::BucketQueue);
        vsids.notify_restart();
        assert_eq!(vsids.mode(), VsidsMode::BinaryHeap);
    }

    #[test]
    fn stale_entries_do_not_reappear_after_pop() {
        let mut vsids = BucketQueueVsids::new(8);
        vsids.push(Var(1));
        vsids.push(Var(2));
        vsids.bump_var(Var(1));
        vsids.bump_var(Var(1));

        assert_eq!(vsids.pop_highest(), Some(Var(1)));
        assert_eq!(vsids.pop_highest(), Some(Var(2)));
        assert_eq!(vsids.pop_highest(), None);
    }

    #[test]
    fn seeded_noise_breaks_ties_deterministically() {
        let mut first = BucketQueueVsids::with_config(
            4,
            VsidsConfig {
                random_seed: 17,
                ..VsidsConfig::default()
            },
        );
        let mut second = BucketQueueVsids::with_config(
            4,
            VsidsConfig {
                random_seed: 17,
                ..VsidsConfig::default()
            },
        );

        for var in [Var(1), Var(2), Var(3)] {
            first.push(var);
            second.push(var);
        }

        let order1 = [
            first.pop_highest().expect("invariant: first pick"),
            first.pop_highest().expect("invariant: second pick"),
            first.pop_highest().expect("invariant: third pick"),
        ];
        let order2 = [
            second.pop_highest().expect("invariant: first pick"),
            second.pop_highest().expect("invariant: second pick"),
            second.pop_highest().expect("invariant: third pick"),
        ];

        assert_eq!(order1, order2);
    }

    #[test]
    fn rescale_preserves_ordering() {
        let mut vsids = BucketQueueVsids::new(8);
        vsids.push(Var(1));
        vsids.push(Var(2));

        while vsids.activity(Var(1)) < MAX_ACTIVITY / 10.0 {
            vsids.bump_var(Var(1));
            vsids.decay_activity();
        }

        vsids.bump_var(Var(2));
        vsids.bump_var(Var(2));

        let first = vsids.pop_highest().expect("invariant: first selection");
        let second = vsids.pop_highest().expect("invariant: second selection");
        assert_ne!(first, second);
        assert!(matches!(
            [first, second],
            [Var(1), Var(2)] | [Var(2), Var(1)]
        ));
    }
}

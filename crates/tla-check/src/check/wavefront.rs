// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symbolic wavefront compression for CDEMC Wave 3.
//!
//! Compresses a set of BFS frontier states into a disjunctive formula
//! that the symbolic engine (BMC) can use to search for violations
//! starting from the entire frontier at once, rather than one state at a time.
//!
//! # Formula Structure
//!
//! Each concrete frontier state becomes a conjunction of variable assignments:
//!
//! ```text
//! state_i = (x = v_x) /\ (y = v_y) /\ ...
//! ```
//!
//! The wavefront formula is the disjunction of all such conjunctions:
//!
//! ```text
//! wavefront = state_1 \/ state_2 \/ ... \/ state_N
//! ```
//!
//! # Common-Value Factoring
//!
//! When a variable has the same value across all (or most) states in
//! the frontier, it is factored out of the per-state disjuncts and
//! asserted once as a shared constraint. This reduces formula size:
//!
//! ```text
//! (x = 5) /\ ((y = 1 /\ z = T) \/ (y = 2 /\ z = F) \/ ...)
//! ```
//!
//! Part of #3794.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};

use num_traits::ToPrimitive;
use tla_z4::BmcValue;

use crate::cooperative_state::FrontierSample;
use crate::state::State;
use crate::Value;

/// Minimum number of frontier states to trigger wavefront compression.
///
/// Below this threshold, individual frontier sampling (Wave 1) is more
/// efficient than building and solving a disjunctive formula.
pub(crate) const WAVEFRONT_THRESHOLD: usize = 100;

/// Minimum entropy score to consider a frontier batch worth compressing.
///
/// Below this threshold, the frontier is too homogeneous (low diversity)
/// to be useful as BMC seeds. Skipping low-entropy batches prevents
/// wasting symbolic engine time on redundant initial states.
///
/// Part of #3845.
pub(crate) const MIN_ENTROPY_THRESHOLD: f64 = 0.3;

/// Entropy score above which a frontier batch is compressed immediately
/// without reservoir sampling. High-entropy batches represent diverse
/// states that are valuable for BMC seeding.
///
/// Part of #3845.
pub(crate) const HIGH_ENTROPY_THRESHOLD: f64 = 2.0;

/// Quality metrics for the wavefront compression pipeline.
///
/// Tracks how many wavefronts are sent, skipped due to low entropy,
/// consumed by BMC, and average entropy across compressed batches.
///
/// Part of #3845.
pub(crate) struct WavefrontMetrics {
    /// Total wavefronts successfully sent to the BMC lane.
    pub(crate) wavefronts_sent: AtomicU64,
    /// Wavefronts skipped because entropy was below [`MIN_ENTROPY_THRESHOLD`].
    pub(crate) wavefronts_skipped_low_entropy: AtomicU64,
    /// Wavefronts consumed by the BMC lane.
    pub(crate) wavefronts_consumed: AtomicU64,
    /// Sum of entropy scores across all evaluated batches (for averaging).
    entropy_sum: AtomicU64,
    /// Number of batches evaluated for entropy (for averaging).
    entropy_count: AtomicU64,
}

impl WavefrontMetrics {
    /// Create a new zero-initialized metrics tracker.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            wavefronts_sent: AtomicU64::new(0),
            wavefronts_skipped_low_entropy: AtomicU64::new(0),
            wavefronts_consumed: AtomicU64::new(0),
            entropy_sum: AtomicU64::new(0),
            entropy_count: AtomicU64::new(0),
        }
    }

    /// Record an entropy observation for a batch.
    pub(crate) fn record_entropy(&self, entropy: f64) {
        // Store as fixed-point: multiply by 1000 to preserve 3 decimal places.
        self.entropy_sum
            .fetch_add((entropy * 1000.0) as u64, Ordering::Relaxed);
        self.entropy_count.fetch_add(1, Ordering::Relaxed);
    }

    /// Average entropy score across all evaluated batches.
    #[must_use]
    pub(crate) fn avg_entropy(&self) -> f64 {
        let count = self.entropy_count.load(Ordering::Relaxed);
        if count == 0 {
            return 0.0;
        }
        let sum = self.entropy_sum.load(Ordering::Relaxed);
        (sum as f64 / 1000.0) / count as f64
    }
}

/// Compute the entropy score for a batch of frontier samples.
///
/// For each variable, counts the number of distinct values across all samples.
/// The score is the average of `log2(distinct_values)` across all variables.
///
/// - Identical samples produce an entropy of 0.0 (all variables have 1 distinct value).
/// - Maximally diverse samples (every variable has a unique value per sample)
///   produce `log2(N)` where N is the sample count.
///
/// Complexity: O(n * v) where n = number of samples, v = number of variables.
///
/// Part of #3845.
#[must_use]
pub(crate) fn entropy_score(samples: &[FrontierSample]) -> f64 {
    if samples.is_empty() {
        return 0.0;
    }

    // Collect all variable names from the first sample.
    let var_names: Vec<&str> = samples[0]
        .assignments
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();

    if var_names.is_empty() {
        return 0.0;
    }

    let mut total_log_distinct = 0.0f64;

    for (var_idx, var_name) in var_names.iter().enumerate() {
        // Count distinct values for this variable across all samples.
        // Use a simple O(n^2) distinct-counting approach for small N,
        // avoiding HashMap overhead.
        let mut seen: Vec<&BmcValue> = Vec::new();

        for sample in samples {
            // Find the variable in this sample's assignments by index
            // (canonical ordering) or by name as fallback.
            let value = if var_idx < sample.assignments.len()
                && sample.assignments[var_idx].0 == *var_name
            {
                &sample.assignments[var_idx].1
            } else {
                // Fallback: search by name.
                match sample.assignments.iter().find(|(n, _)| n == var_name) {
                    Some((_, v)) => v,
                    None => continue,
                }
            };

            if !seen.iter().any(|s| bmc_value_eq(s, value)) {
                seen.push(value);
            }
        }

        let distinct_count = seen.len();
        if distinct_count > 0 {
            total_log_distinct += (distinct_count as f64).log2();
        }
    }

    total_log_distinct / var_names.len() as f64
}

/// Filter a batch of frontier samples based on diversity (entropy).
///
/// - If entropy is below `min_entropy`, returns an empty vec (skip this batch).
/// - Otherwise, returns the input samples unchanged. For batches in the
///   mid-range (between [`MIN_ENTROPY_THRESHOLD`] and [`HIGH_ENTROPY_THRESHOLD`]),
///   callers should use reservoir sampling externally if desired.
///
/// Part of #3845.
#[must_use]
pub(crate) fn diversity_filter(
    samples: &[FrontierSample],
    min_entropy: f64,
) -> Vec<FrontierSample> {
    if samples.is_empty() {
        return Vec::new();
    }

    let score = entropy_score(samples);
    if score < min_entropy {
        return Vec::new();
    }

    samples.to_vec()
}

/// A variable assignment factored out of the per-state disjuncts.
///
/// When a variable has the same value in every state of the frontier,
/// it becomes a shared constraint rather than appearing in each disjunct.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct SharedConstraint {
    /// Variable name.
    pub(crate) name: String,
    /// Common value shared by all frontier states.
    pub(crate) value: BmcValue,
}

/// A single state-conjunction in the disjunctive wavefront formula.
///
/// Contains only the variable assignments that differ across states
/// (shared constraints are factored out into [`WavefrontFormula::shared`]).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct StateConjunct {
    /// Variable name -> concrete value assignments for this state.
    /// Only contains variables NOT in the shared constraints.
    pub(crate) assignments: Vec<(String, BmcValue)>,
}

/// A compressed symbolic formula representing a BFS frontier.
///
/// Structure: `shared_constraints /\ (disjunct_1 \/ disjunct_2 \/ ... \/ disjunct_N)`
///
/// where each `disjunct_i` is a conjunction of per-variable assignments for
/// variables whose values vary across the frontier.
#[derive(Debug, Clone)]
pub(crate) struct WavefrontFormula {
    /// Constraints shared by ALL states (factored out of disjuncts).
    pub(crate) shared: Vec<SharedConstraint>,
    /// Per-state disjuncts containing only varying variable assignments.
    pub(crate) disjuncts: Vec<StateConjunct>,
    /// BFS depth at which this frontier was sampled.
    pub(crate) depth: usize,
    /// Number of original frontier states compressed into this formula.
    pub(crate) source_state_count: usize,
}

impl WavefrontFormula {
    /// Total number of variable assignments in the formula.
    ///
    /// Counts shared constraints once plus all per-disjunct assignments.
    /// Useful for estimating formula complexity.
    #[must_use]
    pub(crate) fn total_assignments(&self) -> usize {
        let shared = self.shared.len();
        let varying: usize = self.disjuncts.iter().map(|d| d.assignments.len()).sum();
        shared + varying
    }

    /// Number of variables that were factored out as shared constraints.
    #[must_use]
    pub(crate) fn shared_count(&self) -> usize {
        self.shared.len()
    }

    /// Number of disjuncts (one per original frontier state).
    #[must_use]
    pub(crate) fn disjunct_count(&self) -> usize {
        self.disjuncts.len()
    }
}

/// Wavefront compressor: transforms a batch of BFS frontier states into
/// a compact symbolic formula.
pub(crate) struct WavefrontCompressor {
    /// Minimum frontier size to trigger compression.
    threshold: usize,
}

impl WavefrontCompressor {
    /// Create a new compressor with the given frontier size threshold.
    #[must_use]
    pub(crate) fn new(threshold: usize) -> Self {
        Self { threshold }
    }

    /// Create a compressor with the default threshold ([`WAVEFRONT_THRESHOLD`]).
    #[must_use]
    pub(crate) fn with_default_threshold() -> Self {
        Self::new(WAVEFRONT_THRESHOLD)
    }

    /// Whether the given frontier is large enough for compression.
    #[must_use]
    pub(crate) fn should_compress(&self, state_count: usize) -> bool {
        state_count >= self.threshold
    }

    /// Compress a set of frontier samples into a wavefront formula.
    ///
    /// # Algorithm
    ///
    /// 1. Collect the set of all variable names across all states.
    /// 2. For each variable, check if all states assign the same value.
    /// 3. Variables with a uniform value become [`SharedConstraint`]s.
    /// 4. Remaining (varying) variables stay in per-state [`StateConjunct`]s.
    ///
    /// Returns `None` if `states` is empty.
    #[must_use]
    pub(crate) fn compress_frontier(&self, states: &[FrontierSample]) -> Option<WavefrontFormula> {
        if states.is_empty() {
            return None;
        }

        let depth = states[0].depth;
        let source_state_count = states.len();

        // Collect all variable names (use first state's ordering as canonical).
        let var_names: Vec<String> = states[0]
            .assignments
            .iter()
            .map(|(name, _)| name.clone())
            .collect();

        // Build per-variable value sets to detect uniform vs varying.
        let mut var_values: HashMap<&str, Vec<&BmcValue>> = HashMap::with_capacity(var_names.len());
        for name in &var_names {
            var_values.insert(name.as_str(), Vec::with_capacity(states.len()));
        }

        for sample in states {
            for (name, value) in &sample.assignments {
                if let Some(vals) = var_values.get_mut(name.as_str()) {
                    vals.push(value);
                }
            }
        }

        // Partition into shared (uniform) and varying variables.
        let mut shared = Vec::new();
        let mut varying_vars: HashSet<&str> = HashSet::new();

        for name in &var_names {
            let vals = &var_values[name.as_str()];
            if vals.len() == states.len() && all_equal(vals) {
                shared.push(SharedConstraint {
                    name: name.clone(),
                    value: vals[0].clone(),
                });
            } else {
                varying_vars.insert(name.as_str());
            }
        }

        // Build per-state disjuncts with only varying variables.
        let disjuncts: Vec<StateConjunct> = states
            .iter()
            .map(|sample| {
                let assignments: Vec<(String, BmcValue)> = sample
                    .assignments
                    .iter()
                    .filter(|(name, _)| varying_vars.contains(name.as_str()))
                    .map(|(name, value)| (name.clone(), value.clone()))
                    .collect();
                StateConjunct { assignments }
            })
            .collect();

        Some(WavefrontFormula {
            shared,
            disjuncts,
            depth,
            source_state_count,
        })
    }
}

// =========================================================================
// State-based compression API (Part of #3794)
// =========================================================================

/// A compressed wavefront produced from raw `State` objects.
///
/// Separates variable assignments into:
/// - `common_assignments`: variables with the same value in ALL input states
/// - `varying_disjuncts`: per-state assignments for variables that differ
///
/// This is the higher-level API counterpart to [`WavefrontFormula`], which
/// operates on pre-converted `FrontierSample` objects. `CompressedWavefront`
/// works directly with `State` objects and handles `Value` -> `BmcValue`
/// conversion internally.
///
/// # Formula Semantics
///
/// ```text
/// common_assignments /\ (varying_disjuncts[0] \/ varying_disjuncts[1] \/ ...)
/// ```
#[derive(Debug, Clone)]
pub(crate) struct CompressedWavefront {
    /// Variable assignments shared by ALL input states.
    ///
    /// Each entry is `(variable_name, value)` where the value was identical
    /// across every state in the compressed batch.
    pub(crate) common_assignments: Vec<(String, BmcValue)>,

    /// Per-state disjuncts for variables whose values differ across states.
    ///
    /// Each inner `Vec` represents one input state's varying assignments.
    /// Variables that appear in `common_assignments` are excluded.
    pub(crate) varying_disjuncts: Vec<Vec<(String, BmcValue)>>,

    /// Number of original states that were compressed (excluding skipped).
    pub(crate) source_state_count: usize,

    /// Number of states that were skipped because they contained
    /// values that could not be converted to `BmcValue` (lazy sets,
    /// closures, FuncSet, intervals exceeding the expansion limit, etc.).
    pub(crate) skipped_non_scalar: usize,
}

impl CompressedWavefront {
    /// Total number of individual variable assignments in the formula.
    ///
    /// Counts common assignments once plus all per-disjunct assignments.
    #[must_use]
    pub(crate) fn total_assignments(&self) -> usize {
        let common = self.common_assignments.len();
        let varying: usize = self.varying_disjuncts.iter().map(Vec::len).sum();
        common + varying
    }

    /// Compression ratio: fraction of total variables that were factored
    /// out as common.
    ///
    /// Returns `0.0` if there are no disjuncts or no variables.
    /// A ratio of `1.0` means all variables are common (perfect compression).
    /// A ratio of `0.0` means no variables are common (no compression).
    #[must_use]
    pub(crate) fn compression_ratio(&self) -> f64 {
        let varying_per_state = self.varying_disjuncts.first().map_or(0, Vec::len);
        let total_vars = self.common_assignments.len() + varying_per_state;
        if total_vars == 0 {
            return 0.0;
        }
        self.common_assignments.len() as f64 / total_vars as f64
    }
}

/// Maximum number of elements when expanding an `Interval` to a concrete `BmcValue::Set`.
///
/// Intervals larger than this are rejected (returns `None`) to prevent
/// accidental formula blowup when a spec uses a wide range like `1..1000000`.
const INTERVAL_EXPANSION_LIMIT: usize = 10_000;

/// Try to convert a TLA+ `Value` to a `BmcValue` for symbolic encoding.
///
/// Supports scalar types (Bool, Int), interned types (String, ModelValue),
/// and compound types (Tuple, Seq, Record, Func, IntFunc, Set, Interval).
///
/// Returns `None` for lazy/non-enumerable types (Subset, FuncSet, RecordSet,
/// TupleSet, SetCup, SetCap, SetDiff, SetPred, KSubset, BigUnion,
/// LazyFunc, closures) since they cannot be concretely expanded without
/// evaluation context or may be exponentially large.
#[must_use]
pub(crate) fn value_to_bmc_value(value: &Value) -> Option<BmcValue> {
    match value {
        Value::Bool(b) => Some(BmcValue::Bool(*b)),
        Value::SmallInt(n) => Some(BmcValue::Int(*n)),
        Value::Int(n) => {
            if let Some(i) = n.to_i64() {
                Some(BmcValue::Int(i))
            } else {
                Some(BmcValue::BigInt((**n).clone()))
            }
        }
        // String -> Int via TLC-compatible string token interning.
        Value::String(s) => {
            let token = tla_value::value::tlc_string_token(s);
            Some(BmcValue::Int(i64::from(token)))
        }
        // ModelValue -> Int via model value registry index.
        Value::ModelValue(name) => {
            let idx = tla_value::value::lookup_model_value_index(name)?;
            Some(BmcValue::Int(i64::from(idx)))
        }
        // Tuple -> Sequence (element-wise recursive conversion).
        Value::Tuple(elems) => {
            let converted: Option<Vec<BmcValue>> = elems.iter().map(value_to_bmc_value).collect();
            Some(BmcValue::Sequence(converted?))
        }
        // Seq -> Sequence (element-wise recursive conversion).
        Value::Seq(seq) => {
            let converted: Option<Vec<BmcValue>> = seq.iter().map(value_to_bmc_value).collect();
            Some(BmcValue::Sequence(converted?))
        }
        // Record -> Sequence (field values in sorted-field-name order).
        // RecordValue entries are already sorted by NameId, and iter_str()
        // resolves to Arc<str> — but since entries are sorted by interned ID
        // (which preserves alphabetical order for field names), we use iter()
        // directly and just take the values.
        Value::Record(rec) => {
            let converted: Option<Vec<BmcValue>> = rec.values().map(value_to_bmc_value).collect();
            Some(BmcValue::Sequence(converted?))
        }
        // Func -> Sequence (interleaved [key, val, key, val, ...]).
        Value::Func(func) => {
            let mut elems = Vec::with_capacity(func.domain_len() * 2);
            for (k, v) in func.iter() {
                elems.push(value_to_bmc_value(k)?);
                elems.push(value_to_bmc_value(v)?);
            }
            Some(BmcValue::Sequence(elems))
        }
        // IntFunc -> Sequence (interleaved [key, val, key, val, ...]).
        Value::IntFunc(func) => {
            let int_func: &tla_value::value::IntIntervalFunc = func;
            let min_key = int_func.min();
            let values = int_func.values();
            let mut elems = Vec::with_capacity(values.len() * 2);
            for (i, v) in values.iter().enumerate() {
                let key = min_key + i as i64;
                elems.push(BmcValue::Int(key));
                elems.push(value_to_bmc_value(v)?);
            }
            Some(BmcValue::Sequence(elems))
        }
        // Set (finite, concrete) -> Set (element-wise recursive conversion).
        Value::Set(sorted_set) => {
            let converted: Option<Vec<BmcValue>> =
                sorted_set.iter().map(value_to_bmc_value).collect();
            Some(BmcValue::Set(converted?))
        }
        // Interval -> Set (expand to concrete elements, with size limit).
        Value::Interval(iv) => {
            let low = iv.low().to_i64()?;
            let high = iv.high().to_i64()?;
            let size = if high >= low {
                (high - low + 1) as usize
            } else {
                0
            };
            if size > INTERVAL_EXPANSION_LIMIT {
                return None;
            }
            let elems: Vec<BmcValue> = (low..=high).map(BmcValue::Int).collect();
            Some(BmcValue::Set(elems))
        }
        // All other types: lazy sets, closures, FuncSet, etc.
        _ => None,
    }
}

impl WavefrontCompressor {
    /// Compress a set of `State` objects into a [`CompressedWavefront`].
    ///
    /// Supports scalar types (Bool, Int), interned types (String, ModelValue),
    /// and compound types (Tuple, Seq, Record, Func, IntFunc, Set, Interval).
    /// States containing values that cannot be converted to `BmcValue`
    /// (lazy sets, closures, FuncSet, etc.) are skipped and counted in
    /// `skipped_non_scalar`.
    ///
    /// # Algorithm
    ///
    /// 1. For each state, extract the named variables (`vars`) and convert
    ///    their values to `BmcValue` via [`value_to_bmc_value`]. States with
    ///    any unconvertible variable are skipped.
    /// 2. For each variable, check if all convertible states assign the
    ///    same value.
    /// 3. Uniform variables become `common_assignments`.
    /// 4. Varying variables stay in per-state `varying_disjuncts`.
    ///
    /// Returns `None` if no states could be converted (all empty or all
    /// contain unconvertible values).
    #[must_use]
    pub(crate) fn compress(
        &self,
        states: &[State],
        vars: &[String],
    ) -> Option<CompressedWavefront> {
        if states.is_empty() || vars.is_empty() {
            return None;
        }

        // Convert State objects to per-state BmcValue assignments.
        // Skip states with any unconvertible variable.
        let mut converted: Vec<Vec<(String, BmcValue)>> = Vec::with_capacity(states.len());
        let mut skipped = 0usize;

        for state in states {
            let mut assignments = Vec::with_capacity(vars.len());
            let mut all_scalar = true;

            for var_name in vars {
                if let Some(value) = state.get(var_name) {
                    if let Some(bmc_val) = value_to_bmc_value(value) {
                        assignments.push((var_name.clone(), bmc_val));
                    } else {
                        all_scalar = false;
                        break;
                    }
                }
                // If variable not present in state, skip it silently.
            }

            if all_scalar && !assignments.is_empty() {
                converted.push(assignments);
            } else {
                skipped += 1;
            }
        }

        if converted.is_empty() {
            return None;
        }

        let source_state_count = converted.len();

        // Build per-variable value vectors to detect uniform vs varying.
        let mut var_values: HashMap<&str, Vec<&BmcValue>> = HashMap::with_capacity(vars.len());
        for var_name in vars {
            var_values.insert(var_name.as_str(), Vec::with_capacity(converted.len()));
        }

        for state_assignments in &converted {
            for (name, value) in state_assignments {
                if let Some(vals) = var_values.get_mut(name.as_str()) {
                    vals.push(value);
                }
            }
        }

        // Partition into common (uniform) and varying variables.
        let mut common_assignments = Vec::new();
        let mut varying_var_names: HashSet<&str> = HashSet::new();

        for var_name in vars {
            let vals = match var_values.get(var_name.as_str()) {
                Some(v) => v,
                None => continue,
            };
            if vals.len() == source_state_count && all_equal(vals) {
                common_assignments.push((var_name.clone(), vals[0].clone()));
            } else if !vals.is_empty() {
                varying_var_names.insert(var_name.as_str());
            }
        }

        // Build per-state disjuncts with only varying variables.
        let varying_disjuncts: Vec<Vec<(String, BmcValue)>> = converted
            .iter()
            .map(|state_assignments| {
                state_assignments
                    .iter()
                    .filter(|(name, _)| varying_var_names.contains(name.as_str()))
                    .map(|(name, value)| (name.clone(), value.clone()))
                    .collect()
            })
            .collect();

        Some(CompressedWavefront {
            common_assignments,
            varying_disjuncts,
            source_state_count,
            skipped_non_scalar: skipped,
        })
    }
}

/// Check whether all values in a slice are equal.
fn all_equal(vals: &[&BmcValue]) -> bool {
    if vals.is_empty() {
        return true;
    }
    let first = vals[0];
    vals.iter().all(|v| bmc_value_eq(v, first))
}

/// Convert a flat i64 buffer (JIT serialized value) to a `BmcValue`.
///
/// The JIT serialization format uses type tags (TAG_INT, TAG_BOOL, etc.)
/// followed by payload. This function translates that representation into
/// the symbolic `BmcValue` that the BMC consumer expects.
///
/// Returns `None` for unsupported or malformed buffers.
#[cfg(feature = "jit")]
fn jit_buf_to_bmc_value(buf: &[i64], pos: usize) -> Option<(BmcValue, usize)> {
    use tla_jit::compound_layout::{
        TAG_BOOL, TAG_FUNC, TAG_INT, TAG_RECORD, TAG_SEQ, TAG_SET, TAG_STRING, TAG_TUPLE,
    };

    if pos >= buf.len() {
        return None;
    }

    let tag = buf[pos];
    match tag {
        TAG_BOOL => {
            if pos + 1 >= buf.len() {
                return None;
            }
            Some((BmcValue::Bool(buf[pos + 1] != 0), 2))
        }
        TAG_INT => {
            if pos + 1 >= buf.len() {
                return None;
            }
            Some((BmcValue::Int(buf[pos + 1]), 2))
        }
        TAG_STRING => {
            // Strings are interned as NameId; encode as Int (matches value_to_bmc_value
            // which uses tlc_string_token). We use the raw NameId here since the JIT
            // serialization stores NameId(u32) as i64.
            if pos + 1 >= buf.len() {
                return None;
            }
            Some((BmcValue::Int(buf[pos + 1]), 2))
        }
        TAG_RECORD => {
            // Record: [TAG_RECORD, field_count, (name_id, value)...]
            // Encode as BmcValue::Sequence of field values (same as value_to_bmc_value).
            if pos + 1 >= buf.len() {
                return None;
            }
            let field_count = buf[pos + 1] as usize;
            let mut offset = pos + 2;
            let mut values = Vec::with_capacity(field_count);
            for _ in 0..field_count {
                if offset >= buf.len() {
                    return None;
                }
                // Skip the name_id word.
                offset += 1;
                let (val, consumed) = jit_buf_to_bmc_value(buf, offset)?;
                offset += consumed;
                values.push(val);
            }
            Some((BmcValue::Sequence(values), offset - pos))
        }
        TAG_SEQ | TAG_TUPLE => {
            // Sequence/Tuple: [TAG, length, elem...]
            // Encode as BmcValue::Sequence.
            if pos + 1 >= buf.len() {
                return None;
            }
            let elem_count = buf[pos + 1] as usize;
            let mut offset = pos + 2;
            let mut elems = Vec::with_capacity(elem_count);
            for _ in 0..elem_count {
                let (val, consumed) = jit_buf_to_bmc_value(buf, offset)?;
                offset += consumed;
                elems.push(val);
            }
            Some((BmcValue::Sequence(elems), offset - pos))
        }
        TAG_SET => {
            // Set: [TAG_SET, cardinality, elem...]
            // Encode as BmcValue::Set.
            if pos + 1 >= buf.len() {
                return None;
            }
            let elem_count = buf[pos + 1] as usize;
            let mut offset = pos + 2;
            let mut elems = Vec::with_capacity(elem_count);
            for _ in 0..elem_count {
                let (val, consumed) = jit_buf_to_bmc_value(buf, offset)?;
                offset += consumed;
                elems.push(val);
            }
            Some((BmcValue::Set(elems), offset - pos))
        }
        TAG_FUNC => {
            // Function: [TAG_FUNC, pair_count, (key, val)...]
            // Encode as BmcValue::Sequence of interleaved [k, v, k, v, ...].
            if pos + 1 >= buf.len() {
                return None;
            }
            let pair_count = buf[pos + 1] as usize;
            let mut offset = pos + 2;
            let mut elems = Vec::with_capacity(pair_count * 2);
            for _ in 0..pair_count {
                let (key, kc) = jit_buf_to_bmc_value(buf, offset)?;
                offset += kc;
                let (val, vc) = jit_buf_to_bmc_value(buf, offset)?;
                offset += vc;
                elems.push(key);
                elems.push(val);
            }
            Some((BmcValue::Sequence(elems), offset - pos))
        }
        _ => None,
    }
}

// =========================================================================
// JIT Wavefront Encoder (Part of #3863)
// =========================================================================

/// Wavefront encoder that uses the JIT's state layout for efficient encoding.
///
/// When the JIT has compiled actions and has a [`StateLayout`] available,
/// this encoder serializes `State` objects through the JIT's flat `[i64]`
/// representation, avoiding the general `value_to_bmc_value` conversion.
///
/// Benefits over the symbolic path:
/// - Handles all value types that the JIT can serialize (records, sequences,
///   sets, functions, tuples) without the lazy-type rejection of `value_to_bmc_value`.
/// - Produces a consistent encoding aligned with JIT-compiled next-state functions.
///
/// Falls back to the existing symbolic `WavefrontCompressor::compress()` path
/// when the JIT layout is not available or serialization fails.
///
/// Part of #3863.
#[cfg(feature = "jit")]
pub(crate) struct JitWavefrontEncoder {
    /// JIT state layout describing the type of each state variable.
    layout: tla_jit::compound_layout::StateLayout,
    /// Variable names in layout order (matching StateLayout var indices).
    var_names: Vec<String>,
    /// Reusable buffer for JIT serialization (avoids per-state allocation).
    buf: Vec<i64>,
}

#[cfg(feature = "jit")]
impl JitWavefrontEncoder {
    /// Create a new JIT wavefront encoder from a state layout and variable names.
    ///
    /// `var_names` must be in the same order as the `StateLayout` var indices
    /// (i.e., `var_names[i]` corresponds to `layout.var_layout(i)`).
    #[must_use]
    pub(crate) fn new(
        layout: tla_jit::compound_layout::StateLayout,
        var_names: Vec<String>,
    ) -> Self {
        debug_assert_eq!(
            layout.var_count(),
            var_names.len(),
            "layout var count must match var_names length"
        );
        Self {
            layout,
            var_names,
            buf: Vec::with_capacity(256),
        }
    }

    /// Encode a single state into `(variable_name, BmcValue)` assignments
    /// using the JIT's serialization format.
    ///
    /// Returns `None` if any variable fails to serialize or convert.
    fn encode_state(&mut self, state: &State) -> Option<Vec<(String, BmcValue)>> {
        let mut assignments = Vec::with_capacity(self.var_names.len());

        for (idx, var_name) in self.var_names.iter().enumerate() {
            let value = state.get(var_name)?;

            // Check if this is a simple scalar that can be encoded directly
            // (avoids the serialize/deserialize round-trip for the common case).
            let _var_layout = self.layout.var_layout(idx);
            match value {
                Value::Bool(b) => {
                    assignments.push((var_name.clone(), BmcValue::Bool(*b)));
                    continue;
                }
                Value::SmallInt(n) => {
                    assignments.push((var_name.clone(), BmcValue::Int(*n)));
                    continue;
                }
                Value::Int(n) => {
                    if let Some(i) = n.to_i64() {
                        assignments.push((var_name.clone(), BmcValue::Int(i)));
                    } else {
                        assignments.push((var_name.clone(), BmcValue::BigInt((**n).clone())));
                    }
                    continue;
                }
                _ => {}
            }

            // Compound value: serialize via JIT layout, then convert to BmcValue.
            self.buf.clear();
            if tla_jit::compound_layout::serialize_value(value, &mut self.buf).is_err() {
                // Serialization failed — fall back to value_to_bmc_value.
                let bmc_val = value_to_bmc_value(value)?;
                assignments.push((var_name.clone(), bmc_val));
                continue;
            }

            // Convert the flat i64 buffer to BmcValue.
            let (bmc_val, _consumed) = jit_buf_to_bmc_value(&self.buf, 0)?;
            assignments.push((var_name.clone(), bmc_val));
        }

        Some(assignments)
    }

    /// Compress a set of `State` objects into a [`CompressedWavefront`] using
    /// the JIT's state layout for encoding.
    ///
    /// States that fail JIT serialization are skipped (counted in
    /// `skipped_non_scalar`). If no states can be encoded, returns `None`.
    ///
    /// The output is fully compatible with the existing BMC consumer — the
    /// `CompressedWavefront` structure is identical to what
    /// `WavefrontCompressor::compress()` produces.
    #[must_use]
    pub(crate) fn compress_states(&mut self, states: &[State]) -> Option<CompressedWavefront> {
        if states.is_empty() || self.var_names.is_empty() {
            return None;
        }

        let mut converted: Vec<Vec<(String, BmcValue)>> = Vec::with_capacity(states.len());
        let mut skipped = 0usize;

        for state in states {
            match self.encode_state(state) {
                Some(assignments) if !assignments.is_empty() => {
                    converted.push(assignments);
                }
                _ => {
                    skipped += 1;
                }
            }
        }

        if converted.is_empty() {
            return None;
        }

        let source_state_count = converted.len();

        // Build per-variable value vectors to detect uniform vs varying.
        let mut var_values: HashMap<&str, Vec<&BmcValue>> =
            HashMap::with_capacity(self.var_names.len());
        for var_name in &self.var_names {
            var_values.insert(var_name.as_str(), Vec::with_capacity(converted.len()));
        }

        for state_assignments in &converted {
            for (name, value) in state_assignments {
                if let Some(vals) = var_values.get_mut(name.as_str()) {
                    vals.push(value);
                }
            }
        }

        // Partition into common (uniform) and varying variables.
        let mut common_assignments = Vec::new();
        let mut varying_var_names: HashSet<&str> = HashSet::new();

        for var_name in &self.var_names {
            let vals = match var_values.get(var_name.as_str()) {
                Some(v) => v,
                None => continue,
            };
            if vals.len() == source_state_count && all_equal(vals) {
                common_assignments.push((var_name.clone(), vals[0].clone()));
            } else if !vals.is_empty() {
                varying_var_names.insert(var_name.as_str());
            }
        }

        // Build per-state disjuncts with only varying variables.
        let varying_disjuncts: Vec<Vec<(String, BmcValue)>> = converted
            .iter()
            .map(|state_assignments| {
                state_assignments
                    .iter()
                    .filter(|(name, _)| varying_var_names.contains(name.as_str()))
                    .map(|(name, value)| (name.clone(), value.clone()))
                    .collect()
            })
            .collect();

        Some(CompressedWavefront {
            common_assignments,
            varying_disjuncts,
            source_state_count,
            skipped_non_scalar: skipped,
        })
    }
}

/// Construct a `JitWavefrontEncoder` from an initial state, inferring the layout.
///
/// This is a convenience function for cases where the JIT state layout was
/// not pre-computed. It infers `VarLayout` from the runtime values of each
/// variable in the initial state.
///
/// Returns `None` if the initial state is empty.
///
/// Part of #3863.
#[cfg(feature = "jit")]
#[must_use]
pub(crate) fn jit_encoder_from_initial_state(initial_state: &State) -> Option<JitWavefrontEncoder> {
    use tla_jit::compound_layout::{infer_var_layout, StateLayout};

    let mut var_names = Vec::new();
    let mut var_layouts = Vec::new();

    for (name, value) in initial_state.vars() {
        var_names.push(name.to_string());
        var_layouts.push(infer_var_layout(value));
    }

    if var_names.is_empty() {
        return None;
    }

    let layout = StateLayout::new(var_layouts);
    Some(JitWavefrontEncoder::new(layout, var_names))
}

/// Structural equality for BmcValue (since it may not implement Eq).
fn bmc_value_eq(a: &BmcValue, b: &BmcValue) -> bool {
    match (a, b) {
        (BmcValue::Bool(a), BmcValue::Bool(b)) => a == b,
        (BmcValue::Int(a), BmcValue::Int(b)) => a == b,
        (BmcValue::BigInt(a), BmcValue::BigInt(b)) => a == b,
        (BmcValue::Set(a), BmcValue::Set(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| bmc_value_eq(x, y))
        }
        (BmcValue::Sequence(a), BmcValue::Sequence(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| bmc_value_eq(x, y))
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn sample(depth: usize, assignments: Vec<(&str, BmcValue)>) -> FrontierSample {
        FrontierSample {
            depth,
            assignments: assignments
                .into_iter()
                .map(|(name, val)| (name.to_string(), val))
                .collect(),
        }
    }

    // =========================================================================
    // WavefrontCompressor tests
    // =========================================================================

    #[test]
    fn test_compress_empty_frontier_returns_none() {
        let compressor = WavefrontCompressor::new(1);
        assert!(compressor.compress_frontier(&[]).is_none());
    }

    #[test]
    fn test_compress_single_state_all_shared() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![sample(
            3,
            vec![("x", BmcValue::Int(1)), ("y", BmcValue::Bool(true))],
        )];
        let formula = compressor.compress_frontier(&states).unwrap();

        assert_eq!(formula.depth, 3);
        assert_eq!(formula.source_state_count, 1);
        // With 1 state, all vars are "shared" (trivially uniform).
        assert_eq!(formula.shared_count(), 2);
        assert_eq!(formula.disjunct_count(), 1);
        // The single disjunct should be empty (all factored out).
        assert!(formula.disjuncts[0].assignments.is_empty());
    }

    #[test]
    fn test_compress_uniform_frontier_all_shared() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            sample(
                5,
                vec![("x", BmcValue::Int(42)), ("y", BmcValue::Bool(false))],
            ),
            sample(
                5,
                vec![("x", BmcValue::Int(42)), ("y", BmcValue::Bool(false))],
            ),
            sample(
                5,
                vec![("x", BmcValue::Int(42)), ("y", BmcValue::Bool(false))],
            ),
        ];
        let formula = compressor.compress_frontier(&states).unwrap();

        assert_eq!(formula.shared_count(), 2);
        assert_eq!(formula.disjunct_count(), 3);
        for d in &formula.disjuncts {
            assert!(d.assignments.is_empty(), "all vars should be shared");
        }
    }

    #[test]
    fn test_compress_varying_frontier_factors_common() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            sample(
                2,
                vec![
                    ("x", BmcValue::Int(1)),
                    ("y", BmcValue::Bool(true)),
                    ("z", BmcValue::Int(99)),
                ],
            ),
            sample(
                2,
                vec![
                    ("x", BmcValue::Int(2)),
                    ("y", BmcValue::Bool(true)),
                    ("z", BmcValue::Int(99)),
                ],
            ),
            sample(
                2,
                vec![
                    ("x", BmcValue::Int(3)),
                    ("y", BmcValue::Bool(true)),
                    ("z", BmcValue::Int(99)),
                ],
            ),
        ];
        let formula = compressor.compress_frontier(&states).unwrap();

        // y and z are uniform -> shared; x varies -> per-disjunct.
        assert_eq!(formula.shared_count(), 2);
        let shared_names: Vec<&str> = formula.shared.iter().map(|s| s.name.as_str()).collect();
        assert!(shared_names.contains(&"y"));
        assert!(shared_names.contains(&"z"));

        assert_eq!(formula.disjunct_count(), 3);
        for d in &formula.disjuncts {
            assert_eq!(d.assignments.len(), 1, "only x should vary");
            assert_eq!(d.assignments[0].0, "x");
        }

        // Verify x values.
        let x_values: Vec<&BmcValue> = formula
            .disjuncts
            .iter()
            .map(|d| &d.assignments[0].1)
            .collect();
        assert!(x_values.contains(&&BmcValue::Int(1)));
        assert!(x_values.contains(&&BmcValue::Int(2)));
        assert!(x_values.contains(&&BmcValue::Int(3)));
    }

    #[test]
    fn test_compress_all_varying() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            sample(
                0,
                vec![("x", BmcValue::Int(1)), ("y", BmcValue::Bool(true))],
            ),
            sample(
                0,
                vec![("x", BmcValue::Int(2)), ("y", BmcValue::Bool(false))],
            ),
        ];
        let formula = compressor.compress_frontier(&states).unwrap();

        // No shared constraints — both variables differ.
        assert_eq!(formula.shared_count(), 0);
        assert_eq!(formula.disjunct_count(), 2);
        assert_eq!(formula.disjuncts[0].assignments.len(), 2);
        assert_eq!(formula.disjuncts[1].assignments.len(), 2);
    }

    #[test]
    fn test_total_assignments_count() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            sample(
                0,
                vec![
                    ("x", BmcValue::Int(1)),
                    ("y", BmcValue::Bool(true)),
                    ("z", BmcValue::Int(10)),
                ],
            ),
            sample(
                0,
                vec![
                    ("x", BmcValue::Int(2)),
                    ("y", BmcValue::Bool(true)),
                    ("z", BmcValue::Int(20)),
                ],
            ),
        ];
        let formula = compressor.compress_frontier(&states).unwrap();

        // y is shared (1 constraint), x and z vary (2 per disjunct * 2 disjuncts = 4)
        // total = 1 + 4 = 5
        assert_eq!(formula.total_assignments(), 5);
    }

    #[test]
    fn test_should_compress_respects_threshold() {
        let compressor = WavefrontCompressor::new(100);
        assert!(!compressor.should_compress(99));
        assert!(compressor.should_compress(100));
        assert!(compressor.should_compress(200));
    }

    // =========================================================================
    // BmcValue equality tests
    // =========================================================================

    #[test]
    fn test_bmc_value_eq_basic() {
        assert!(bmc_value_eq(&BmcValue::Int(1), &BmcValue::Int(1)));
        assert!(!bmc_value_eq(&BmcValue::Int(1), &BmcValue::Int(2)));
        assert!(bmc_value_eq(&BmcValue::Bool(true), &BmcValue::Bool(true)));
        assert!(!bmc_value_eq(&BmcValue::Bool(true), &BmcValue::Bool(false)));
        assert!(!bmc_value_eq(&BmcValue::Int(1), &BmcValue::Bool(true)));
    }

    #[test]
    fn test_bmc_value_eq_sets() {
        let a = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]);
        let b = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2)]);
        let c = BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(3)]);
        assert!(bmc_value_eq(&a, &b));
        assert!(!bmc_value_eq(&a, &c));
    }

    // =========================================================================
    // value_to_bmc_value conversion tests
    // =========================================================================

    #[test]
    fn test_value_to_bmc_value_bool() {
        assert_eq!(
            value_to_bmc_value(&Value::Bool(true)),
            Some(BmcValue::Bool(true))
        );
        assert_eq!(
            value_to_bmc_value(&Value::Bool(false)),
            Some(BmcValue::Bool(false))
        );
    }

    #[test]
    fn test_value_to_bmc_value_small_int() {
        assert_eq!(
            value_to_bmc_value(&Value::SmallInt(42)),
            Some(BmcValue::Int(42))
        );
        assert_eq!(
            value_to_bmc_value(&Value::SmallInt(-1)),
            Some(BmcValue::Int(-1))
        );
        assert_eq!(
            value_to_bmc_value(&Value::SmallInt(0)),
            Some(BmcValue::Int(0))
        );
    }

    #[test]
    fn test_value_to_bmc_value_big_int_fits_i64() {
        use num_bigint::BigInt;
        let big = Value::Int(Arc::new(BigInt::from(999_999)));
        assert_eq!(value_to_bmc_value(&big), Some(BmcValue::Int(999_999)));
    }

    #[test]
    fn test_value_to_bmc_value_string_returns_int() {
        // String values are interned to integer tokens.
        let s = Value::String(Arc::from("hello"));
        let result = value_to_bmc_value(&s);
        assert!(result.is_some(), "strings should convert via interning");
        match result.unwrap() {
            BmcValue::Int(n) => assert!(n >= 0, "token should be non-negative"),
            other => panic!("expected BmcValue::Int, got {other:?}"),
        }
    }

    #[test]
    fn test_value_to_bmc_value_set_returns_set() {
        // Finite concrete sets are now supported.
        let set_val = Value::set([Value::SmallInt(1), Value::SmallInt(2)]);
        let result = value_to_bmc_value(&set_val);
        assert!(result.is_some(), "finite sets should convert");
        match result.unwrap() {
            BmcValue::Set(elems) => assert_eq!(elems.len(), 2),
            other => panic!("expected BmcValue::Set, got {other:?}"),
        }
    }

    #[test]
    fn test_value_to_bmc_value_tuple_returns_sequence() {
        let tuple = Value::Tuple(Arc::from(vec![Value::SmallInt(1), Value::Bool(true)]));
        let result = value_to_bmc_value(&tuple);
        assert_eq!(
            result,
            Some(BmcValue::Sequence(vec![
                BmcValue::Int(1),
                BmcValue::Bool(true)
            ]))
        );
    }

    #[test]
    fn test_value_to_bmc_value_lazy_returns_none() {
        // Lazy/non-enumerable types still return None.
        use tla_value::value::SubsetValue;
        let subset = Value::Subset(SubsetValue::new(Value::set([Value::SmallInt(1)])));
        assert_eq!(value_to_bmc_value(&subset), None);
    }

    // =========================================================================
    // State-based compress() tests (Part of #3794)
    // =========================================================================

    /// Helper to build a State from (name, Value) pairs.
    fn make_state(pairs: Vec<(&str, Value)>) -> State {
        State::from_pairs(pairs.into_iter().map(|(k, v)| (k, v)))
    }

    #[test]
    fn test_compress_state_empty_returns_none() {
        let compressor = WavefrontCompressor::new(1);
        let vars = vec!["x".to_string()];
        assert!(compressor.compress(&[], &vars).is_none());
    }

    #[test]
    fn test_compress_state_empty_vars_returns_none() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![make_state(vec![("x", Value::SmallInt(1))])];
        assert!(compressor.compress(&states, &[]).is_none());
    }

    #[test]
    fn test_compress_state_single_state_all_common() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![make_state(vec![
            ("x", Value::SmallInt(5)),
            ("y", Value::Bool(true)),
        ])];
        let vars = vec!["x".to_string(), "y".to_string()];
        let cw = compressor.compress(&states, &vars).unwrap();

        assert_eq!(cw.source_state_count, 1);
        assert_eq!(cw.skipped_non_scalar, 0);
        // Single state: all vars are common.
        assert_eq!(cw.common_assignments.len(), 2);
        assert_eq!(cw.varying_disjuncts.len(), 1);
        assert!(cw.varying_disjuncts[0].is_empty());
    }

    #[test]
    fn test_compress_state_factors_common_variables() {
        let compressor = WavefrontCompressor::new(1);
        // x varies, y is constant, z is constant.
        let states = vec![
            make_state(vec![
                ("x", Value::SmallInt(1)),
                ("y", Value::Bool(true)),
                ("z", Value::SmallInt(99)),
            ]),
            make_state(vec![
                ("x", Value::SmallInt(2)),
                ("y", Value::Bool(true)),
                ("z", Value::SmallInt(99)),
            ]),
            make_state(vec![
                ("x", Value::SmallInt(3)),
                ("y", Value::Bool(true)),
                ("z", Value::SmallInt(99)),
            ]),
        ];
        let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let cw = compressor.compress(&states, &vars).unwrap();

        assert_eq!(cw.source_state_count, 3);
        assert_eq!(cw.skipped_non_scalar, 0);

        // y and z are common.
        let common_names: Vec<&str> = cw
            .common_assignments
            .iter()
            .map(|(n, _)| n.as_str())
            .collect();
        assert!(common_names.contains(&"y"));
        assert!(common_names.contains(&"z"));
        assert_eq!(cw.common_assignments.len(), 2);

        // x varies across 3 disjuncts.
        assert_eq!(cw.varying_disjuncts.len(), 3);
        for disjunct in &cw.varying_disjuncts {
            assert_eq!(disjunct.len(), 1, "only x should vary");
            assert_eq!(disjunct[0].0, "x");
        }

        // Verify x values.
        let x_vals: Vec<&BmcValue> = cw.varying_disjuncts.iter().map(|d| &d[0].1).collect();
        assert!(x_vals.contains(&&BmcValue::Int(1)));
        assert!(x_vals.contains(&&BmcValue::Int(2)));
        assert!(x_vals.contains(&&BmcValue::Int(3)));
    }

    #[test]
    fn test_compress_state_all_varying() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            make_state(vec![("x", Value::SmallInt(1)), ("y", Value::Bool(true))]),
            make_state(vec![("x", Value::SmallInt(2)), ("y", Value::Bool(false))]),
        ];
        let vars = vec!["x".to_string(), "y".to_string()];
        let cw = compressor.compress(&states, &vars).unwrap();

        assert_eq!(cw.common_assignments.len(), 0);
        assert_eq!(cw.varying_disjuncts.len(), 2);
        assert_eq!(cw.varying_disjuncts[0].len(), 2);
        assert_eq!(cw.varying_disjuncts[1].len(), 2);
    }

    #[test]
    fn test_compress_state_skips_unconvertible_states() {
        use tla_value::value::SubsetValue;
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            // State 1: all convertible — should be included.
            make_state(vec![("x", Value::SmallInt(1)), ("y", Value::Bool(true))]),
            // State 2: contains a lazy SUBSET — should be skipped.
            make_state(vec![
                ("x", Value::SmallInt(2)),
                (
                    "y",
                    Value::Subset(SubsetValue::new(Value::set([Value::SmallInt(10)]))),
                ),
            ]),
            // State 3: all convertible — should be included.
            make_state(vec![("x", Value::SmallInt(3)), ("y", Value::Bool(false))]),
        ];
        let vars = vec!["x".to_string(), "y".to_string()];
        let cw = compressor.compress(&states, &vars).unwrap();

        assert_eq!(
            cw.source_state_count, 2,
            "only 2 convertible states included"
        );
        assert_eq!(
            cw.skipped_non_scalar, 1,
            "1 state skipped for unconvertible y"
        );
        assert_eq!(cw.varying_disjuncts.len(), 2);
    }

    #[test]
    fn test_compress_state_all_unconvertible_returns_none() {
        use tla_value::value::SubsetValue;
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            make_state(vec![(
                "x",
                Value::Subset(SubsetValue::new(Value::set([Value::SmallInt(1)]))),
            )]),
            make_state(vec![(
                "x",
                Value::Subset(SubsetValue::new(Value::set([Value::SmallInt(2)]))),
            )]),
        ];
        let vars = vec!["x".to_string()];
        assert!(
            compressor.compress(&states, &vars).is_none(),
            "all states unconvertible should return None"
        );
    }

    #[test]
    fn test_compress_state_total_assignments() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            make_state(vec![
                ("x", Value::SmallInt(1)),
                ("y", Value::Bool(true)),
                ("z", Value::SmallInt(10)),
            ]),
            make_state(vec![
                ("x", Value::SmallInt(2)),
                ("y", Value::Bool(true)),
                ("z", Value::SmallInt(20)),
            ]),
        ];
        let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let cw = compressor.compress(&states, &vars).unwrap();

        // y is common (1), x and z vary (2 per disjunct * 2 disjuncts = 4)
        // total = 1 + 4 = 5
        assert_eq!(cw.total_assignments(), 5);
    }

    #[test]
    fn test_compress_state_compression_ratio() {
        let compressor = WavefrontCompressor::new(1);

        // 2 of 3 vars are common => ratio = 2/3
        let states = vec![
            make_state(vec![
                ("x", Value::SmallInt(1)),
                ("y", Value::Bool(true)),
                ("z", Value::SmallInt(99)),
            ]),
            make_state(vec![
                ("x", Value::SmallInt(2)),
                ("y", Value::Bool(true)),
                ("z", Value::SmallInt(99)),
            ]),
        ];
        let vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];
        let cw = compressor.compress(&states, &vars).unwrap();
        let ratio = cw.compression_ratio();
        assert!(
            (ratio - 2.0 / 3.0).abs() < 1e-10,
            "expected ratio ~0.667, got {ratio}"
        );
    }

    #[test]
    fn test_compress_state_uniform_frontier_perfect_compression() {
        let compressor = WavefrontCompressor::new(1);
        let states = vec![
            make_state(vec![("x", Value::SmallInt(5)), ("y", Value::Bool(false))]),
            make_state(vec![("x", Value::SmallInt(5)), ("y", Value::Bool(false))]),
            make_state(vec![("x", Value::SmallInt(5)), ("y", Value::Bool(false))]),
        ];
        let vars = vec!["x".to_string(), "y".to_string()];
        let cw = compressor.compress(&states, &vars).unwrap();

        assert_eq!(cw.common_assignments.len(), 2);
        for d in &cw.varying_disjuncts {
            assert!(d.is_empty(), "all vars should be common");
        }
        let ratio = cw.compression_ratio();
        assert!(
            (ratio - 1.0).abs() < 1e-10,
            "expected perfect compression ratio 1.0, got {ratio}"
        );
    }

    // =========================================================================
    // Entropy score tests (Part of #3845)
    // =========================================================================

    #[test]
    fn test_entropy_score_empty_samples() {
        assert_eq!(entropy_score(&[]), 0.0);
    }

    #[test]
    fn test_entropy_score_identical_samples_zero_entropy() {
        // All samples are identical -> 1 distinct value per var -> log2(1) = 0.
        let states = vec![
            sample(
                0,
                vec![("x", BmcValue::Int(5)), ("y", BmcValue::Bool(true))],
            ),
            sample(
                0,
                vec![("x", BmcValue::Int(5)), ("y", BmcValue::Bool(true))],
            ),
            sample(
                0,
                vec![("x", BmcValue::Int(5)), ("y", BmcValue::Bool(true))],
            ),
        ];
        let score = entropy_score(&states);
        assert!(
            score.abs() < 1e-10,
            "identical samples should have entropy 0.0, got {score}"
        );
    }

    #[test]
    fn test_entropy_score_uniform_high_entropy() {
        // 4 samples, each variable has 4 distinct values -> log2(4) = 2.0.
        let states = vec![
            sample(0, vec![("x", BmcValue::Int(1)), ("y", BmcValue::Int(10))]),
            sample(0, vec![("x", BmcValue::Int(2)), ("y", BmcValue::Int(20))]),
            sample(0, vec![("x", BmcValue::Int(3)), ("y", BmcValue::Int(30))]),
            sample(0, vec![("x", BmcValue::Int(4)), ("y", BmcValue::Int(40))]),
        ];
        let score = entropy_score(&states);
        // Both x and y have 4 distinct values -> avg(log2(4), log2(4)) = 2.0.
        assert!(
            (score - 2.0).abs() < 1e-10,
            "expected entropy 2.0, got {score}"
        );
    }

    #[test]
    fn test_entropy_score_mixed_variance() {
        // x has 3 distinct values, y has 1 distinct value.
        // Expected: avg(log2(3), log2(1)) = log2(3) / 2 ≈ 0.792.
        let states = vec![
            sample(
                0,
                vec![("x", BmcValue::Int(1)), ("y", BmcValue::Bool(true))],
            ),
            sample(
                0,
                vec![("x", BmcValue::Int(2)), ("y", BmcValue::Bool(true))],
            ),
            sample(
                0,
                vec![("x", BmcValue::Int(3)), ("y", BmcValue::Bool(true))],
            ),
        ];
        let score = entropy_score(&states);
        let expected = 3.0f64.log2() / 2.0;
        assert!(
            (score - expected).abs() < 1e-10,
            "expected entropy {expected}, got {score}"
        );
    }

    #[test]
    fn test_entropy_score_single_variable() {
        // 2 samples, 1 variable, 2 distinct values -> log2(2) = 1.0.
        let states = vec![
            sample(0, vec![("x", BmcValue::Int(1))]),
            sample(0, vec![("x", BmcValue::Int(2))]),
        ];
        let score = entropy_score(&states);
        assert!(
            (score - 1.0).abs() < 1e-10,
            "expected entropy 1.0, got {score}"
        );
    }

    // =========================================================================
    // Diversity filter tests (Part of #3845)
    // =========================================================================

    #[test]
    fn test_diversity_filter_skips_low_entropy_batch() {
        // All identical -> entropy = 0.0 < MIN_ENTROPY_THRESHOLD -> empty result.
        let states = vec![
            sample(
                0,
                vec![("x", BmcValue::Int(5)), ("y", BmcValue::Bool(true))],
            ),
            sample(
                0,
                vec![("x", BmcValue::Int(5)), ("y", BmcValue::Bool(true))],
            ),
            sample(
                0,
                vec![("x", BmcValue::Int(5)), ("y", BmcValue::Bool(true))],
            ),
        ];
        let filtered = diversity_filter(&states, MIN_ENTROPY_THRESHOLD);
        assert!(
            filtered.is_empty(),
            "low-entropy batch should be skipped, got {} samples",
            filtered.len()
        );
    }

    #[test]
    fn test_diversity_filter_passes_high_entropy_batch() {
        // 4 samples, all unique -> entropy = 2.0 > MIN_ENTROPY_THRESHOLD.
        let states = vec![
            sample(0, vec![("x", BmcValue::Int(1)), ("y", BmcValue::Int(10))]),
            sample(0, vec![("x", BmcValue::Int(2)), ("y", BmcValue::Int(20))]),
            sample(0, vec![("x", BmcValue::Int(3)), ("y", BmcValue::Int(30))]),
            sample(0, vec![("x", BmcValue::Int(4)), ("y", BmcValue::Int(40))]),
        ];
        let filtered = diversity_filter(&states, MIN_ENTROPY_THRESHOLD);
        assert_eq!(
            filtered.len(),
            4,
            "high-entropy batch should pass through unchanged"
        );
    }

    #[test]
    fn test_diversity_filter_empty_input() {
        let filtered = diversity_filter(&[], MIN_ENTROPY_THRESHOLD);
        assert!(filtered.is_empty());
    }

    // =========================================================================
    // WavefrontMetrics tests (Part of #3845)
    // =========================================================================

    #[test]
    fn test_wavefront_metrics_initial_values() {
        let metrics = WavefrontMetrics::new();
        assert_eq!(metrics.wavefronts_sent.load(Ordering::Relaxed), 0);
        assert_eq!(
            metrics
                .wavefronts_skipped_low_entropy
                .load(Ordering::Relaxed),
            0
        );
        assert_eq!(metrics.wavefronts_consumed.load(Ordering::Relaxed), 0);
        assert_eq!(metrics.avg_entropy(), 0.0);
    }

    #[test]
    fn test_wavefront_metrics_avg_entropy() {
        let metrics = WavefrontMetrics::new();
        metrics.record_entropy(1.0);
        metrics.record_entropy(3.0);
        let avg = metrics.avg_entropy();
        assert!(
            (avg - 2.0).abs() < 0.01,
            "expected avg entropy ~2.0, got {avg}"
        );
    }

    // =========================================================================
    // JIT Wavefront Encoder tests (Part of #3863)
    // =========================================================================

    #[cfg(feature = "jit")]
    mod jit_encoder_tests {
        use super::*;
        use tla_jit::compound_layout::{StateLayout, VarLayout};

        /// Build a state layout for all-scalar (Int/Bool) variables.
        fn scalar_layout(var_types: &[VarLayout]) -> StateLayout {
            StateLayout::new(var_types.to_vec())
        }

        #[test]
        fn test_jit_encoder_scalar_states_match_symbolic() {
            // Create states with scalar variables.
            let states = vec![
                make_state(vec![("x", Value::SmallInt(1)), ("y", Value::Bool(true))]),
                make_state(vec![("x", Value::SmallInt(2)), ("y", Value::Bool(false))]),
                make_state(vec![("x", Value::SmallInt(3)), ("y", Value::Bool(true))]),
            ];
            let vars = vec!["x".to_string(), "y".to_string()];

            // Symbolic path.
            let compressor = WavefrontCompressor::new(1);
            let symbolic = compressor
                .compress(&states, &vars)
                .expect("symbolic compress");

            // JIT path.
            let layout = scalar_layout(&[VarLayout::ScalarInt, VarLayout::ScalarBool]);
            let mut encoder = JitWavefrontEncoder::new(layout, vars.clone());
            let jit = encoder.compress_states(&states).expect("jit compress");

            // Both should produce the same results.
            assert_eq!(
                symbolic.source_state_count, jit.source_state_count,
                "source state counts must match"
            );
            assert_eq!(
                symbolic.common_assignments.len(),
                jit.common_assignments.len(),
                "common assignment counts must match"
            );
            assert_eq!(
                symbolic.varying_disjuncts.len(),
                jit.varying_disjuncts.len(),
                "disjunct counts must match"
            );

            // Common assignment names should match.
            let sym_common_names: Vec<&str> = symbolic
                .common_assignments
                .iter()
                .map(|(n, _)| n.as_str())
                .collect();
            let jit_common_names: Vec<&str> = jit
                .common_assignments
                .iter()
                .map(|(n, _)| n.as_str())
                .collect();
            assert_eq!(sym_common_names, jit_common_names);

            // Per-disjunct varying variable counts should match.
            for (i, (sym_d, jit_d)) in symbolic
                .varying_disjuncts
                .iter()
                .zip(jit.varying_disjuncts.iter())
                .enumerate()
            {
                assert_eq!(
                    sym_d.len(),
                    jit_d.len(),
                    "disjunct {i} varying var counts must match"
                );
            }
        }

        #[test]
        fn test_jit_encoder_uniform_frontier_all_common() {
            let states = vec![
                make_state(vec![("x", Value::SmallInt(5)), ("y", Value::Bool(false))]),
                make_state(vec![("x", Value::SmallInt(5)), ("y", Value::Bool(false))]),
            ];
            let vars = vec!["x".to_string(), "y".to_string()];
            let layout = scalar_layout(&[VarLayout::ScalarInt, VarLayout::ScalarBool]);
            let mut encoder = JitWavefrontEncoder::new(layout, vars);
            let cw = encoder.compress_states(&states).expect("compress");

            // All variables are uniform -> all common.
            assert_eq!(cw.common_assignments.len(), 2);
            for d in &cw.varying_disjuncts {
                assert!(d.is_empty(), "all vars should be common");
            }
            assert_eq!(cw.source_state_count, 2);
            assert_eq!(cw.skipped_non_scalar, 0);
        }

        #[test]
        fn test_jit_encoder_empty_states_returns_none() {
            let layout = scalar_layout(&[VarLayout::ScalarInt]);
            let mut encoder = JitWavefrontEncoder::new(layout, vec!["x".to_string()]);
            assert!(encoder.compress_states(&[]).is_none());
        }

        #[test]
        fn test_jit_encoder_compound_sequence_state() {
            use tla_jit::compound_layout::CompoundLayout;
            use tla_value::value::SeqValue;

            // States with a sequence variable.
            let seq1 = Value::Seq(Arc::new(SeqValue::from_vec(vec![
                Value::SmallInt(10),
                Value::SmallInt(20),
            ])));
            let seq2 = Value::Seq(Arc::new(SeqValue::from_vec(vec![
                Value::SmallInt(30),
                Value::SmallInt(40),
            ])));

            let states = vec![
                make_state(vec![("x", Value::SmallInt(1)), ("s", seq1)]),
                make_state(vec![("x", Value::SmallInt(2)), ("s", seq2)]),
            ];
            let vars = vec!["s".to_string(), "x".to_string()];

            let layout = StateLayout::new(vec![
                VarLayout::Compound(CompoundLayout::Sequence {
                    element_layout: Box::new(CompoundLayout::Int),
                }),
                VarLayout::ScalarInt,
            ]);
            let mut encoder = JitWavefrontEncoder::new(layout, vars.clone());
            let jit_cw = encoder
                .compress_states(&states)
                .expect("jit compress compound");

            // x varies, s varies -> both should be in varying_disjuncts.
            assert_eq!(jit_cw.source_state_count, 2);
            assert_eq!(jit_cw.skipped_non_scalar, 0);
            assert_eq!(jit_cw.varying_disjuncts.len(), 2);

            // Compare with symbolic path.
            let compressor = WavefrontCompressor::new(1);
            let sym_cw = compressor
                .compress(&states, &vars)
                .expect("symbolic compress");

            assert_eq!(sym_cw.source_state_count, jit_cw.source_state_count);
            assert_eq!(
                sym_cw.common_assignments.len(),
                jit_cw.common_assignments.len()
            );
            assert_eq!(
                sym_cw.varying_disjuncts.len(),
                jit_cw.varying_disjuncts.len()
            );
        }

        #[test]
        fn test_jit_encoder_from_initial_state() {
            let state = make_state(vec![("a", Value::SmallInt(10)), ("b", Value::Bool(true))]);
            let encoder = jit_encoder_from_initial_state(&state);
            assert!(encoder.is_some(), "should infer layout from initial state");
            let encoder = encoder.unwrap();
            assert_eq!(encoder.var_names.len(), 2);
            assert_eq!(encoder.layout.var_count(), 2);
        }

        #[test]
        fn test_jit_encoder_from_empty_state_returns_none() {
            let state = make_state(vec![]);
            assert!(jit_encoder_from_initial_state(&state).is_none());
        }

        #[test]
        fn test_jit_buf_to_bmc_value_scalar_int() {
            use tla_jit::compound_layout::TAG_INT;
            let buf = vec![TAG_INT, 42];
            let (val, consumed) = super::jit_buf_to_bmc_value(&buf, 0).unwrap();
            assert_eq!(val, BmcValue::Int(42));
            assert_eq!(consumed, 2);
        }

        #[test]
        fn test_jit_buf_to_bmc_value_scalar_bool() {
            use tla_jit::compound_layout::TAG_BOOL;
            let buf = vec![TAG_BOOL, 1];
            let (val, consumed) = super::jit_buf_to_bmc_value(&buf, 0).unwrap();
            assert_eq!(val, BmcValue::Bool(true));
            assert_eq!(consumed, 2);
        }

        #[test]
        fn test_jit_buf_to_bmc_value_sequence() {
            use tla_jit::compound_layout::{TAG_INT, TAG_SEQ};
            let buf = vec![TAG_SEQ, 2, TAG_INT, 10, TAG_INT, 20];
            let (val, consumed) = super::jit_buf_to_bmc_value(&buf, 0).unwrap();
            assert_eq!(
                val,
                BmcValue::Sequence(vec![BmcValue::Int(10), BmcValue::Int(20)])
            );
            assert_eq!(consumed, 6);
        }

        #[test]
        fn test_jit_buf_to_bmc_value_set() {
            use tla_jit::compound_layout::{TAG_INT, TAG_SET};
            let buf = vec![TAG_SET, 3, TAG_INT, 1, TAG_INT, 2, TAG_INT, 3];
            let (val, consumed) = super::jit_buf_to_bmc_value(&buf, 0).unwrap();
            assert_eq!(
                val,
                BmcValue::Set(vec![BmcValue::Int(1), BmcValue::Int(2), BmcValue::Int(3)])
            );
            assert_eq!(consumed, 8);
        }

        #[test]
        fn test_jit_buf_to_bmc_value_empty_buffer() {
            assert!(super::jit_buf_to_bmc_value(&[], 0).is_none());
        }

        #[test]
        fn test_jit_buf_to_bmc_value_unknown_tag() {
            let buf = vec![999, 0];
            assert!(super::jit_buf_to_bmc_value(&buf, 0).is_none());
        }
    }
}

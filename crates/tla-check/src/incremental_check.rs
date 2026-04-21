// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental model checking: reuse prior verification results when the spec changes.
//!
//! When a spec is re-checked after a small edit, a full BFS re-exploration is wasteful.
//! This module saves a "verification cache" after each successful run and, on re-check,
//! computes an AST-level diff to identify which actions changed. States reachable
//! **only** through unchanged actions are retained from the cache; states reachable
//! through changed actions are marked "dirty" and re-explored from scratch.
//!
//! # Cache layout
//!
//! The cache directory (`--incremental <DIR>`) contains:
//! - `cache.json` — metadata: spec/config hashes, per-action content hashes,
//!   result summary, state counts
//! - `fingerprints.bin` — binary fingerprint set from the prior run
//! - `provenance.json` — per-state action provenance (which action produced each state)
//! - `successors.json` — successor graph for dirty-state propagation
//!
//! # Safety invariant
//!
//! **Correctness is non-negotiable.** When in doubt, the incremental checker falls
//! back to a full re-check. The cache is purely an optimisation; removing it always
//! produces the same result (just slower).

use crate::coverage::detect_actions;
use crate::state::Fingerprint;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::{self, BufWriter, Write as _};
use std::path::Path;
use tla_core::ast::OperatorDef;

/// Version tag for cache format compatibility.
const CACHE_VERSION: u32 = 1;

// ─────────────────────────────────────────────────────────────────────────────
// Serialisable cache metadata
// ─────────────────────────────────────────────────────────────────────────────

/// Persisted metadata written alongside the fingerprint set after each run.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IncrementalCacheMetadata {
    /// Format version for forward compatibility.
    pub version: u32,
    /// SHA-256 of the spec file content.
    pub spec_hash: String,
    /// SHA-256 of the config file content.
    pub config_hash: String,
    /// Per-action content hashes keyed by action name.
    ///
    /// Computed from the textual representation of each action's AST body.
    /// When a re-check finds that some action hashes differ, only states
    /// reachable through those actions need re-exploration.
    pub action_hashes: FxHashMap<String, String>,
    /// Names of invariants checked on the prior run.
    pub invariant_names: Vec<String>,
    /// Names of properties checked on the prior run.
    pub property_names: Vec<String>,
    /// Whether the previous run completed successfully (no violations).
    pub was_success: bool,
    /// Total distinct states from the prior run.
    pub states_found: usize,
    /// Init operator name.
    pub init_name: String,
    /// Next operator name.
    pub next_name: String,
}

/// Per-state action provenance: records which action produced each state.
///
/// This is the key data structure for incremental re-checking. When an action
/// changes, all states whose provenance includes that action are "dirty" and
/// must be re-explored (along with their transitive successors).
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ActionProvenance {
    /// Maps fingerprint → set of action names that produced transitions *into*
    /// this state. A state is dirty if any of its provenance actions changed.
    entries: FxHashMap<u64, Vec<String>>,
}

impl ActionProvenance {
    /// Create a new empty provenance tracker.
    pub fn new() -> Self {
        Self {
            entries: FxHashMap::default(),
        }
    }

    /// Record that `action_name` produced a transition into the state with
    /// fingerprint `fp`.
    pub fn record(&mut self, fp: Fingerprint, action_name: &str) {
        self.entries
            .entry(fp.0)
            .or_default()
            .push(action_name.to_string());
    }

    /// Record that `fp` was produced by Init (no action).
    pub fn record_init(&mut self, fp: Fingerprint) {
        self.entries
            .entry(fp.0)
            .or_insert_with(|| vec!["__init__".to_string()]);
    }

    /// Return all action names that contributed to this state.
    #[must_use]
    pub fn get_actions(&self, fp: Fingerprint) -> Option<&[String]> {
        self.entries.get(&fp.0).map(|v| v.as_slice())
    }
}

/// Successor graph: records which states each state can reach.
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct SuccessorMap {
    /// Maps parent fingerprint → list of successor fingerprints.
    entries: FxHashMap<u64, Vec<u64>>,
}

impl SuccessorMap {
    /// Create a new empty successor map.
    pub fn new() -> Self {
        Self {
            entries: FxHashMap::default(),
        }
    }

    /// Record that `parent` has successor `child`.
    pub fn record(&mut self, parent: Fingerprint, child: Fingerprint) {
        self.entries.entry(parent.0).or_default().push(child.0);
    }

    /// Get all successors of `parent`.
    #[must_use]
    pub fn get_successors(&self, parent: Fingerprint) -> Option<&[u64]> {
        self.entries.get(&parent.0).map(|v| v.as_slice())
    }

    /// Get all fingerprints that have recorded successors.
    pub fn all_parents(&self) -> impl Iterator<Item = Fingerprint> + '_ {
        self.entries.keys().map(|&k| Fingerprint(k))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Cache I/O
// ─────────────────────────────────────────────────────────────────────────────

/// The on-disk verification cache for incremental model checking.
#[derive(Debug)]
pub struct IncrementalCache {
    /// Metadata about the cached run.
    pub metadata: IncrementalCacheMetadata,
    /// Fingerprints of all states from the prior run.
    pub fingerprints: Vec<Fingerprint>,
    /// Per-state action provenance.
    pub provenance: ActionProvenance,
    /// Successor graph from the prior run.
    pub successors: SuccessorMap,
}

impl IncrementalCache {
    /// Save the cache to `dir`.
    pub fn save(&self, dir: &Path) -> io::Result<()> {
        fs::create_dir_all(dir)?;

        // Metadata JSON
        let meta_path = dir.join("cache.json");
        let meta_file = File::create(&meta_path)?;
        let mut writer = BufWriter::new(meta_file);
        serde_json::to_writer_pretty(&mut writer, &self.metadata)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
        writer.flush()?;

        // Fingerprints (binary, same format as checkpoint)
        crate::checkpoint::binary_io_save_fingerprints(
            &self.fingerprints,
            dir.join("fingerprints.bin"),
        )?;

        // Action provenance (JSON for debuggability)
        let prov_file = File::create(dir.join("provenance.json"))?;
        let mut prov_writer = BufWriter::new(prov_file);
        serde_json::to_writer(&mut prov_writer, &self.provenance)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
        prov_writer.flush()?;

        // Successor graph (JSON)
        let succ_file = File::create(dir.join("successors.json"))?;
        let mut succ_writer = BufWriter::new(succ_file);
        serde_json::to_writer(&mut succ_writer, &self.successors)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))?;
        succ_writer.flush()?;

        Ok(())
    }

    /// Load the cache from `dir`. Returns `None` if the cache does not exist
    /// or is corrupt/incompatible.
    pub fn load(dir: &Path) -> Option<Self> {
        let meta_path = dir.join("cache.json");
        if !meta_path.exists() {
            return None;
        }
        let meta_file = File::open(&meta_path).ok()?;
        let metadata: IncrementalCacheMetadata =
            serde_json::from_reader(io::BufReader::new(meta_file)).ok()?;

        if metadata.version != CACHE_VERSION {
            eprintln!(
                "incremental: cache version mismatch (expected {}, got {}), full re-check",
                CACHE_VERSION, metadata.version
            );
            return None;
        }

        let fingerprints =
            crate::checkpoint::binary_io_load_fingerprints(dir.join("fingerprints.bin")).ok()?;

        let prov_file = File::open(dir.join("provenance.json")).ok()?;
        let provenance: ActionProvenance =
            serde_json::from_reader(io::BufReader::new(prov_file)).ok()?;

        let succ_file = File::open(dir.join("successors.json")).ok()?;
        let successors: SuccessorMap =
            serde_json::from_reader(io::BufReader::new(succ_file)).ok()?;

        Some(IncrementalCache {
            metadata,
            fingerprints,
            provenance,
            successors,
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// AST-level action hashing
// ─────────────────────────────────────────────────────────────────────────────

/// Compute a deterministic content hash of an operator definition's body.
///
/// This gives us a stable way to detect when a particular action's definition
/// has changed between runs.
fn hash_operator_body(def: &OperatorDef) -> String {
    let mut hasher = Sha256::new();
    // Use the Debug representation of the expression as a stable text encoding.
    // This captures structural changes but is insensitive to whitespace/comments.
    let body_text = format!("{:?}", def.body);
    hasher.update(body_text.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Compute per-action content hashes from the Next operator's detected actions.
///
/// Also hashes the Init definition if available. Action hashes are keyed by
/// action name; the Init predicate uses the sentinel key `"__init__"`.
pub fn compute_action_hashes(
    op_defs: &FxHashMap<String, OperatorDef>,
    next_name: &str,
) -> FxHashMap<String, String> {
    let mut hashes = FxHashMap::default();

    if let Some(next_def) = op_defs.get(next_name) {
        let actions = detect_actions(next_def);
        for action in &actions {
            let mut hasher = Sha256::new();
            let expr_text = format!("{:?}", action.expr);
            hasher.update(expr_text.as_bytes());
            let hash = format!("{:x}", hasher.finalize());
            hashes.insert(action.name.clone(), hash);
        }
    }

    // Also hash the Init definition if available
    if let Some(init_def) = op_defs.get("Init") {
        hashes.insert("__init__".to_string(), hash_operator_body(init_def));
    }

    hashes
}

// ─────────────────────────────────────────────────────────────────────────────
// Incremental diff and dirty-state identification
// ─────────────────────────────────────────────────────────────────────────────

/// Result of comparing old and new spec action hashes.
#[derive(Debug)]
pub struct SpecDiff {
    /// Actions whose definitions changed (or were added/removed).
    pub changed_actions: FxHashSet<String>,
    /// Whether the Init predicate changed.
    pub init_changed: bool,
    /// Whether structural changes make incremental re-use impossible
    /// (e.g., config changed, invariants changed).
    pub requires_full_recheck: bool,
}

/// Compare old cache metadata against current spec state.
fn compute_spec_diff(
    cache: &IncrementalCacheMetadata,
    current_action_hashes: &FxHashMap<String, String>,
    current_config_hash: &str,
    current_invariant_names: &[String],
    current_property_names: &[String],
) -> SpecDiff {
    let mut changed_actions = FxHashSet::default();
    let mut init_changed = false;
    let mut requires_full_recheck = false;

    // Config changed? Must do full re-check (constants, symmetry, etc. may differ).
    if cache.config_hash != current_config_hash {
        eprintln!("incremental: config file changed, full re-check required");
        requires_full_recheck = true;
        return SpecDiff {
            changed_actions,
            init_changed: true,
            requires_full_recheck,
        };
    }

    // Invariant set changed? Must re-check all states against new invariants.
    if cache.invariant_names != current_invariant_names {
        eprintln!("incremental: invariant set changed, full re-check required");
        requires_full_recheck = true;
        return SpecDiff {
            changed_actions,
            init_changed: true,
            requires_full_recheck,
        };
    }

    // Property set changed? Must re-check.
    if cache.property_names != current_property_names {
        eprintln!("incremental: property set changed, full re-check required");
        requires_full_recheck = true;
        return SpecDiff {
            changed_actions,
            init_changed: true,
            requires_full_recheck,
        };
    }

    // Compare per-action hashes
    let old_actions: FxHashSet<&str> = cache.action_hashes.keys().map(|s| s.as_str()).collect();
    let new_actions: FxHashSet<&str> = current_action_hashes.keys().map(|s| s.as_str()).collect();

    // Actions added in new spec
    for &name in new_actions.difference(&old_actions) {
        changed_actions.insert(name.to_string());
        if name == "__init__" {
            init_changed = true;
        }
    }

    // Actions removed from spec
    for &name in old_actions.difference(&new_actions) {
        changed_actions.insert(name.to_string());
        if name == "__init__" {
            init_changed = true;
        }
    }

    // Actions present in both: compare hashes
    for &name in old_actions.intersection(&new_actions) {
        let old_hash = &cache.action_hashes[name];
        let new_hash = &current_action_hashes[name];
        if old_hash != new_hash {
            changed_actions.insert(name.to_string());
            if name == "__init__" {
                init_changed = true;
            }
        }
    }

    // If actions were added or removed (structural change), we need full re-check
    // because the Next relation structure changed.
    if old_actions.difference(&new_actions).next().is_some()
        || new_actions.difference(&old_actions).next().is_some()
    {
        eprintln!("incremental: action set structure changed, full re-check required");
        requires_full_recheck = true;
    }

    SpecDiff {
        changed_actions,
        init_changed,
        requires_full_recheck,
    }
}

/// Given a set of changed actions and the cached provenance/successor graph,
/// identify all "dirty" fingerprints that need re-exploration.
///
/// A state is dirty if:
/// 1. It was produced by a changed action (direct dependency), OR
/// 2. It is transitively reachable from a dirty state through the successor graph
///
/// Returns the set of dirty fingerprints and the set of clean (reusable) fingerprints.
pub fn identify_dirty_states(
    cache: &IncrementalCache,
    changed_actions: &FxHashSet<String>,
) -> (FxHashSet<Fingerprint>, FxHashSet<Fingerprint>) {
    let all_fps: FxHashSet<Fingerprint> = cache.fingerprints.iter().copied().collect();

    // Phase 1: Mark directly-dirty states (those produced by changed actions)
    let mut dirty: FxHashSet<Fingerprint> = FxHashSet::default();
    for &fp in &cache.fingerprints {
        if let Some(actions) = cache.provenance.get_actions(fp) {
            for action_name in actions {
                if changed_actions.contains(action_name) {
                    dirty.insert(fp);
                    break;
                }
            }
        }
    }

    // Phase 2: Propagate dirtiness through successor graph (BFS)
    let mut queue: Vec<Fingerprint> = dirty.iter().copied().collect();
    while let Some(fp) = queue.pop() {
        if let Some(succs) = cache.successors.get_successors(fp) {
            for &succ_raw in succs {
                let succ_fp = Fingerprint(succ_raw);
                if !dirty.contains(&succ_fp) && all_fps.contains(&succ_fp) {
                    dirty.insert(succ_fp);
                    queue.push(succ_fp);
                }
            }
        }
    }

    // Clean states = all states minus dirty states
    let clean: FxHashSet<Fingerprint> = all_fps.difference(&dirty).copied().collect();

    (dirty, clean)
}

// ─────────────────────────────────────────────────────────────────────────────
// Public API for incremental checking integration
// ─────────────────────────────────────────────────────────────────────────────

/// Attempt to load and validate an incremental cache for the current run.
///
/// Returns `Some((cache, diff))` if the cache is valid and incremental
/// re-checking is possible; returns `None` if a full re-check is needed.
pub fn try_load_incremental(
    cache_dir: &Path,
    _current_spec_hash: &str,
    current_config_hash: &str,
    current_action_hashes: &FxHashMap<String, String>,
    current_invariant_names: &[String],
    current_property_names: &[String],
) -> Option<(IncrementalCache, SpecDiff)> {
    let cache = IncrementalCache::load(cache_dir)?;

    // If previous run found a violation, don't reuse (the fix might be in the current spec)
    if !cache.metadata.was_success {
        eprintln!("incremental: prior run had violations, full re-check required");
        return None;
    }

    let diff = compute_spec_diff(
        &cache.metadata,
        current_action_hashes,
        current_config_hash,
        current_invariant_names,
        current_property_names,
    );

    if diff.requires_full_recheck {
        return None;
    }

    // If nothing changed at all, we can skip the check entirely
    if diff.changed_actions.is_empty() {
        eprintln!(
            "incremental: spec unchanged, reusing prior result ({} states verified)",
            cache.metadata.states_found
        );
    } else {
        eprintln!(
            "incremental: {} action(s) changed: {:?}",
            diff.changed_actions.len(),
            diff.changed_actions,
        );
    }

    Some((cache, diff))
}

/// Save an incremental cache after a model checking run.
#[allow(clippy::too_many_arguments)]
pub fn save_incremental_cache(
    cache_dir: &Path,
    spec_hash: &str,
    config_hash: &str,
    action_hashes: FxHashMap<String, String>,
    invariant_names: &[String],
    property_names: &[String],
    was_success: bool,
    states_found: usize,
    init_name: &str,
    next_name: &str,
    fingerprints: Vec<Fingerprint>,
    provenance: ActionProvenance,
    successors: SuccessorMap,
) -> io::Result<()> {
    let cache = IncrementalCache {
        metadata: IncrementalCacheMetadata {
            version: CACHE_VERSION,
            spec_hash: spec_hash.to_string(),
            config_hash: config_hash.to_string(),
            action_hashes,
            invariant_names: invariant_names.to_vec(),
            property_names: property_names.to_vec(),
            was_success,
            states_found,
            init_name: init_name.to_string(),
            next_name: next_name.to_string(),
        },
        fingerprints,
        provenance,
        successors,
    };
    cache.save(cache_dir)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_action_provenance_record_and_get() {
        let mut prov = ActionProvenance::new();
        let fp = Fingerprint(42);
        prov.record(fp, "ActionA");
        prov.record(fp, "ActionB");

        let actions = prov.get_actions(fp).expect("should have actions");
        assert_eq!(actions.len(), 2);
        assert!(actions.contains(&"ActionA".to_string()));
        assert!(actions.contains(&"ActionB".to_string()));
    }

    #[test]
    fn test_action_provenance_init() {
        let mut prov = ActionProvenance::new();
        let fp = Fingerprint(1);
        prov.record_init(fp);

        let actions = prov.get_actions(fp).expect("should have init");
        assert_eq!(actions, &["__init__".to_string()]);
    }

    #[test]
    fn test_successor_map_record_and_get() {
        let mut succ = SuccessorMap::new();
        let parent = Fingerprint(1);
        let child1 = Fingerprint(2);
        let child2 = Fingerprint(3);
        succ.record(parent, child1);
        succ.record(parent, child2);

        let children = succ.get_successors(parent).expect("should have successors");
        assert_eq!(children.len(), 2);
        assert!(children.contains(&2));
        assert!(children.contains(&3));
    }

    #[test]
    fn test_spec_diff_no_changes() {
        let meta = IncrementalCacheMetadata {
            version: CACHE_VERSION,
            spec_hash: "abc".to_string(),
            config_hash: "def".to_string(),
            action_hashes: [("A".to_string(), "h1".to_string())].into_iter().collect(),
            invariant_names: vec!["TypeOK".to_string()],
            property_names: vec![],
            was_success: true,
            states_found: 10,
            init_name: "Init".to_string(),
            next_name: "Next".to_string(),
        };

        let current_hashes: FxHashMap<String, String> =
            [("A".to_string(), "h1".to_string())].into_iter().collect();

        let diff = compute_spec_diff(&meta, &current_hashes, "def", &["TypeOK".to_string()], &[]);

        assert!(diff.changed_actions.is_empty());
        assert!(!diff.init_changed);
        assert!(!diff.requires_full_recheck);
    }

    #[test]
    fn test_spec_diff_action_changed() {
        let meta = IncrementalCacheMetadata {
            version: CACHE_VERSION,
            spec_hash: "abc".to_string(),
            config_hash: "def".to_string(),
            action_hashes: [("A".to_string(), "h1".to_string())].into_iter().collect(),
            invariant_names: vec!["TypeOK".to_string()],
            property_names: vec![],
            was_success: true,
            states_found: 10,
            init_name: "Init".to_string(),
            next_name: "Next".to_string(),
        };

        let current_hashes: FxHashMap<String, String> =
            [("A".to_string(), "h2_different".to_string())]
                .into_iter()
                .collect();

        let diff = compute_spec_diff(&meta, &current_hashes, "def", &["TypeOK".to_string()], &[]);

        assert!(diff.changed_actions.contains("A"));
        assert!(!diff.requires_full_recheck);
    }

    #[test]
    fn test_spec_diff_config_changed() {
        let meta = IncrementalCacheMetadata {
            version: CACHE_VERSION,
            spec_hash: "abc".to_string(),
            config_hash: "def".to_string(),
            action_hashes: FxHashMap::default(),
            invariant_names: vec![],
            property_names: vec![],
            was_success: true,
            states_found: 10,
            init_name: "Init".to_string(),
            next_name: "Next".to_string(),
        };

        let diff = compute_spec_diff(&meta, &FxHashMap::default(), "DIFFERENT", &[], &[]);

        assert!(diff.requires_full_recheck);
    }

    #[test]
    fn test_identify_dirty_states_direct() {
        let mut prov = ActionProvenance::new();
        let fp1 = Fingerprint(1);
        let fp2 = Fingerprint(2);
        let fp3 = Fingerprint(3);
        prov.record_init(fp1);
        prov.record(fp2, "ActionA");
        prov.record(fp3, "ActionB");

        let cache = IncrementalCache {
            metadata: IncrementalCacheMetadata {
                version: CACHE_VERSION,
                spec_hash: String::new(),
                config_hash: String::new(),
                action_hashes: FxHashMap::default(),
                invariant_names: vec![],
                property_names: vec![],
                was_success: true,
                states_found: 3,
                init_name: "Init".to_string(),
                next_name: "Next".to_string(),
            },
            fingerprints: vec![fp1, fp2, fp3],
            provenance: prov,
            successors: SuccessorMap::new(),
        };

        let mut changed = FxHashSet::default();
        changed.insert("ActionA".to_string());

        let (dirty, clean) = identify_dirty_states(&cache, &changed);

        assert!(
            dirty.contains(&fp2),
            "fp2 should be dirty (ActionA changed)"
        );
        assert!(!dirty.contains(&fp1), "fp1 should be clean (init only)");
        assert!(
            !dirty.contains(&fp3),
            "fp3 should be clean (ActionB unchanged)"
        );
        assert!(clean.contains(&fp1));
        assert!(clean.contains(&fp3));
    }

    #[test]
    fn test_identify_dirty_states_transitive() {
        let mut prov = ActionProvenance::new();
        let fp1 = Fingerprint(1);
        let fp2 = Fingerprint(2);
        let fp3 = Fingerprint(3);
        prov.record_init(fp1);
        prov.record(fp2, "ActionA");
        prov.record(fp3, "ActionB"); // ActionB unchanged, but reachable from fp2

        let mut succ = SuccessorMap::new();
        succ.record(fp2, fp3); // fp2 -> fp3

        let cache = IncrementalCache {
            metadata: IncrementalCacheMetadata {
                version: CACHE_VERSION,
                spec_hash: String::new(),
                config_hash: String::new(),
                action_hashes: FxHashMap::default(),
                invariant_names: vec![],
                property_names: vec![],
                was_success: true,
                states_found: 3,
                init_name: "Init".to_string(),
                next_name: "Next".to_string(),
            },
            fingerprints: vec![fp1, fp2, fp3],
            provenance: prov,
            successors: succ,
        };

        let mut changed = FxHashSet::default();
        changed.insert("ActionA".to_string());

        let (dirty, clean) = identify_dirty_states(&cache, &changed);

        assert!(dirty.contains(&fp2), "fp2 dirty: ActionA changed");
        assert!(
            dirty.contains(&fp3),
            "fp3 dirty: transitively reachable from dirty fp2"
        );
        assert!(clean.contains(&fp1), "fp1 clean: init only");
    }

    #[test]
    fn test_cache_round_trip() {
        let dir = std::env::temp_dir().join("tla2_incr_cache_test");
        let _ = fs::remove_dir_all(&dir);

        let mut prov = ActionProvenance::new();
        prov.record_init(Fingerprint(1));
        prov.record(Fingerprint(2), "ActionA");

        let mut succ = SuccessorMap::new();
        succ.record(Fingerprint(1), Fingerprint(2));

        let cache = IncrementalCache {
            metadata: IncrementalCacheMetadata {
                version: CACHE_VERSION,
                spec_hash: "spec123".to_string(),
                config_hash: "cfg456".to_string(),
                action_hashes: [("A".to_string(), "hash_a".to_string())]
                    .into_iter()
                    .collect(),
                invariant_names: vec!["TypeOK".to_string()],
                property_names: vec![],
                was_success: true,
                states_found: 2,
                init_name: "Init".to_string(),
                next_name: "Next".to_string(),
            },
            fingerprints: vec![Fingerprint(1), Fingerprint(2)],
            provenance: prov,
            successors: succ,
        };

        cache.save(&dir).expect("save should succeed");

        let loaded = IncrementalCache::load(&dir).expect("load should succeed");
        assert_eq!(loaded.metadata.spec_hash, "spec123");
        assert_eq!(loaded.metadata.states_found, 2);
        assert_eq!(loaded.fingerprints.len(), 2);

        let _ = fs::remove_dir_all(&dir);
    }
}

// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Checkpoint/resume support for model checking.
//!
//! This module provides facilities to save and restore model checking state,
//! enabling long-running checks to be interrupted and resumed later.
//!
//! # Design
//!
//! A checkpoint contains:
//! - **Fingerprints**: Set of seen state fingerprints
//! - **Frontier**: Queue of states still to be explored
//! - **Parent map**: Parent fingerprint for each state (for trace reconstruction)
//! - **Depths**: Depth of each state in the BFS tree
//! - **Statistics**: State counts, transitions, etc.
//!
//! The checkpoint is stored as a directory containing:
//! - `checkpoint.json`: Metadata and statistics
//! - `fingerprints.bin`: Binary fingerprint set
//! - `frontier.json`: States to explore (JSON for debuggability)
//! - `parents.bin`: Parent pointer map
//! - `depths.bin`: Depth map
//!
//! # Usage
//!
//! ```rust,no_run
//! use tla_check::Checkpoint;
//!
//! # fn main() -> std::io::Result<()> {
//! // Serialize a checkpoint to disk.
//! let checkpoint = Checkpoint::new().with_paths(Some("Spec.tla"), Some("Spec.cfg"));
//! checkpoint.save("/path/to/checkpoint")?;
//!
//! // Load it back.
//! let _loaded = Checkpoint::load("/path/to/checkpoint")?;
//! # Ok(())
//! # }
//! ```

mod binary_io;
mod serializable;

pub use serializable::{SerializableState, SerializableValue};

use crate::check::CheckStats;
use crate::state::{Fingerprint, State};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, BufWriter, Read as _, Write};
use std::path::Path;
use std::time::SystemTime;

/// Checkpoint version
const CHECKPOINT_VERSION: u32 = 1;

/// Checkpoint metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckpointMetadata {
    /// Checkpoint format version
    pub version: u32,
    /// When the checkpoint was created
    pub created_at: String,
    /// Spec file path (for verification)
    pub spec_path: Option<String>,
    /// Config file path (for verification)
    pub config_path: Option<String>,
    /// SHA-256 hash of the spec file contents at checkpoint time.
    ///
    /// Used to detect spec modifications between checkpoint save and resume.
    /// Path-only validation is insufficient: a user might edit the spec file
    /// without changing its path, and resuming against a modified spec would
    /// produce incorrect results silently.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub spec_hash: Option<String>,
    /// SHA-256 hash of the config file contents at checkpoint time.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub config_hash: Option<String>,
    /// Model checking statistics at checkpoint time
    pub stats: CheckpointStats,
}

/// Statistics stored in checkpoint
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct CheckpointStats {
    pub states_found: usize,
    pub initial_states: usize,
    pub transitions: usize,
    pub max_depth: usize,
    pub frontier_size: usize,
}

impl From<&CheckStats> for CheckpointStats {
    fn from(stats: &CheckStats) -> Self {
        CheckpointStats {
            states_found: stats.states_found,
            initial_states: stats.initial_states,
            transitions: stats.transitions,
            max_depth: stats.max_depth,
            frontier_size: 0, // Set separately
        }
    }
}

/// A complete model checking checkpoint
#[derive(Debug)]
pub struct Checkpoint {
    /// Metadata about the checkpoint
    pub metadata: CheckpointMetadata,
    /// Seen state fingerprints
    pub fingerprints: Vec<Fingerprint>,
    /// States in the frontier (to be explored)
    pub frontier: Vec<State>,
    /// Parent pointers: child fingerprint -> parent fingerprint
    pub parents: HashMap<Fingerprint, Fingerprint>,
    /// Depth of each state
    pub depths: HashMap<Fingerprint, usize>,
    /// First invariant violation found in continue_on_error mode.
    /// Stores (invariant_name, violating_state_fingerprint).
    /// Without this, a violation discovered before checkpoint would be lost on resume.
    pub first_violation: Option<(String, Fingerprint)>,
    /// First action-level PROPERTY violation found in continue_on_error mode.
    pub first_action_property_violation: Option<(String, Fingerprint)>,
    /// Trace states for the first violation (initial → violating state).
    ///
    /// Populated at checkpoint creation when `store_full_states` is true.
    /// On resume, these states are used directly instead of trying to
    /// reconstruct the trace from the (empty) `seen` DashMap.
    ///
    /// Part of #3112: parallel checkpoint-resume trace reconstruction.
    pub first_violation_trace: Vec<State>,
}

impl Checkpoint {
    /// Create a new empty checkpoint
    pub fn new() -> Self {
        let now = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        Checkpoint {
            metadata: CheckpointMetadata {
                version: CHECKPOINT_VERSION,
                created_at: format!("{}", now),
                spec_path: None,
                config_path: None,
                spec_hash: None,
                config_hash: None,
                stats: CheckpointStats::default(),
            },
            fingerprints: Vec::new(),
            frontier: Vec::new(),
            parents: HashMap::new(),
            depths: HashMap::new(),
            first_violation: None,
            first_action_property_violation: None,
            first_violation_trace: Vec::new(),
        }
    }

    /// Set spec and config paths for verification on resume
    pub fn with_paths(mut self, spec_path: Option<&str>, config_path: Option<&str>) -> Self {
        self.metadata.spec_path = spec_path.map(std::string::ToString::to_string);
        self.metadata.config_path = config_path.map(std::string::ToString::to_string);
        self
    }

    /// Save checkpoint to a directory.
    ///
    /// Uses atomic write-to-temp-then-rename to prevent a crash mid-save from
    /// corrupting the only checkpoint copy. Part of #1780.
    pub fn save<P: AsRef<Path>>(&self, dir: P) -> io::Result<()> {
        let dir = dir.as_ref();

        // Paths for the atomic swap dance:
        //   .saving  — temp dir where new files are written
        //   .old     — previous checkpoint moved aside before rename
        let saving_dir = dir.with_extension("saving");
        let old_dir = dir.with_extension("old");

        // Clean up any stale temp directories from a prior interrupted save.
        if saving_dir.exists() {
            fs::remove_dir_all(&saving_dir)?;
        }
        if old_dir.exists() {
            fs::remove_dir_all(&old_dir)?;
        }

        fs::create_dir_all(&saving_dir)?;

        // Write all files into the temp directory.
        self.save_to_dir(&saving_dir)?;

        // Atomic swap: move old dir aside, rename temp to final.
        if dir.exists() {
            fs::rename(dir, &old_dir)?;
        }
        if let Err(e) = fs::rename(&saving_dir, dir) {
            // Attempt recovery: restore old dir.
            if old_dir.exists() {
                let _ = fs::rename(&old_dir, dir);
            }
            return Err(e);
        }

        // Fsync the parent directory so the rename is durable on crash.
        // On Linux/ext4, rename() updates the directory entry but doesn't
        // guarantee the entry reaches disk without an explicit fsync.
        if let Some(parent) = dir.parent() {
            if let Ok(parent_dir) = File::open(parent) {
                let _ = parent_dir.sync_all();
            }
        }

        // Best-effort cleanup of the old directory.
        if old_dir.exists() {
            let _ = fs::remove_dir_all(&old_dir);
        }

        Ok(())
    }

    /// Write all checkpoint files into `dir` (which must already exist).
    fn save_to_dir(&self, dir: &Path) -> io::Result<()> {
        // Save metadata
        let meta_path = dir.join("checkpoint.json");
        let mut meta = self.metadata.clone();
        meta.stats.frontier_size = self.frontier.len();
        let meta_file = File::create(&meta_path)?;
        let mut writer = BufWriter::new(meta_file);
        serde_json::to_writer_pretty(&mut writer, &meta).map_err(|e| {
            io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e))
        })?;
        writer.flush()?;
        writer.get_ref().sync_all()?;

        // Save fingerprints (binary)
        binary_io::save_fingerprints(&self.fingerprints, dir.join("fingerprints.bin"))?;

        // Save frontier (JSON for debuggability)
        binary_io::save_frontier(&self.frontier, dir.join("frontier.json"))?;

        // Save parent pointers (binary)
        binary_io::save_parents(&self.parents, dir.join("parents.bin"))?;

        // Save depths (binary)
        binary_io::save_depths(&self.depths, dir.join("depths.bin"))?;

        // Save first_violation if present (continue_on_error mode).
        if let Some((ref invariant, ref fp)) = self.first_violation {
            let violation_data = serde_json::json!({
                "invariant": invariant,
                "fingerprint": fp.0,
            });
            let violation_file = File::create(dir.join("first_violation.json"))?;
            let mut vw = BufWriter::new(violation_file);
            serde_json::to_writer_pretty(&mut vw, &violation_data).map_err(|e| {
                io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e))
            })?;
            vw.flush()?;
            vw.get_ref().sync_all()?;
        }

        if let Some((ref property, ref fp)) = self.first_action_property_violation {
            let violation_data = serde_json::json!({
                "property": property,
                "fingerprint": fp.0,
            });
            let violation_file = File::create(dir.join("first_action_property_violation.json"))?;
            let mut vw = BufWriter::new(violation_file);
            serde_json::to_writer_pretty(&mut vw, &violation_data).map_err(|e| {
                io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e))
            })?;
            vw.flush()?;
            vw.get_ref().sync_all()?;
        }

        // Part of #3112: Save violation trace states if available.
        if !self.first_violation_trace.is_empty() {
            binary_io::save_frontier(
                &self.first_violation_trace,
                dir.join("first_violation_trace.json"),
            )?;
        }

        Ok(())
    }

    /// Load checkpoint from a directory.
    ///
    /// If a prior `save()` was interrupted, attempts recovery from the `.old`
    /// backup directory. Part of #1780.
    pub fn load<P: AsRef<Path>>(dir: P) -> io::Result<Self> {
        let dir = dir.as_ref();

        // Recovery: if main dir is missing but .old exists, a prior save was
        // interrupted between renaming old aside and renaming temp to final.
        let old_dir = dir.with_extension("old");
        if !dir.exists() && old_dir.exists() {
            fs::rename(&old_dir, dir)?;
        }
        // Clean up stale temp from interrupted save (data is incomplete).
        let saving_dir = dir.with_extension("saving");
        if saving_dir.exists() {
            let _ = fs::remove_dir_all(&saving_dir);
        }

        // Load metadata
        let meta_path = dir.join("checkpoint.json");
        let meta_file = File::open(&meta_path)?;
        let metadata: CheckpointMetadata = serde_json::from_reader(io::BufReader::new(meta_file))
            .map_err(|e| {
            io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e))
        })?;

        if metadata.version != CHECKPOINT_VERSION {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Checkpoint version mismatch: expected {}, got {}",
                    CHECKPOINT_VERSION, metadata.version
                ),
            ));
        }

        // Load components via binary_io
        let fingerprints = binary_io::load_fingerprints(dir.join("fingerprints.bin"))?;
        let frontier = binary_io::load_frontier(dir.join("frontier.json"))?;
        let parents = binary_io::load_parents(dir.join("parents.bin"))?;
        let depths = binary_io::load_depths(dir.join("depths.bin"))?;

        // Load first_violation if present (backwards compatible — file may not exist)
        let first_violation = binary_io::load_first_violation(dir.join("first_violation.json"))?;
        let first_action_property_violation = binary_io::load_first_action_property_violation(
            dir.join("first_action_property_violation.json"),
        )?;

        // Part of #3112: Load violation trace if present (backwards compatible).
        let trace_path = dir.join("first_violation_trace.json");
        let first_violation_trace = if trace_path.exists() {
            binary_io::load_frontier(trace_path)?
        } else {
            Vec::new()
        };

        Ok(Checkpoint {
            metadata,
            fingerprints,
            frontier,
            parents,
            depths,
            first_violation,
            first_action_property_violation,
            first_violation_trace,
        })
    }

    /// Save fingerprints to binary file (delegate for test access).
    #[cfg(test)]
    fn save_fingerprints<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        binary_io::save_fingerprints(&self.fingerprints, path)
    }

    /// Load fingerprints from binary file (delegate for test access).
    #[cfg(test)]
    fn load_fingerprints<P: AsRef<Path>>(path: P) -> io::Result<Vec<Fingerprint>> {
        binary_io::load_fingerprints(path)
    }

    /// Load parent pointers from binary file (delegate for test access).
    #[cfg(test)]
    fn load_parents<P: AsRef<Path>>(path: P) -> io::Result<HashMap<Fingerprint, Fingerprint>> {
        binary_io::load_parents(path)
    }

    /// Load depths from binary file (delegate for test access).
    #[cfg(test)]
    fn load_depths<P: AsRef<Path>>(path: P) -> io::Result<HashMap<Fingerprint, usize>> {
        binary_io::load_depths(path)
    }
}

impl Default for Checkpoint {
    fn default() -> Self {
        Self::new()
    }
}

/// Compute the SHA-256 hex digest of a file's contents.
///
/// Returns `None` if the file cannot be read (e.g., does not exist).
/// This is intentionally non-fatal: checkpoint creation should not fail
/// just because the spec file has been moved since the checker started.
pub fn compute_file_hash(path: &Path) -> Option<String> {
    let mut file = File::open(path).ok()?;
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 8192];
    loop {
        let n = file.read(&mut buf).ok()?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    Some(format!("{:x}", hasher.finalize()))
}

/// Re-export fingerprint binary I/O for crate-internal consumers (incremental cache).
pub(crate) fn binary_io_save_fingerprints(
    fps: &[crate::state::Fingerprint],
    path: impl AsRef<Path>,
) -> io::Result<()> {
    binary_io::save_fingerprints(fps, path)
}

/// Re-export fingerprint binary I/O for crate-internal consumers (incremental cache).
pub(crate) fn binary_io_load_fingerprints(
    path: impl AsRef<Path>,
) -> io::Result<Vec<crate::state::Fingerprint>> {
    binary_io::load_fingerprints(path)
}

#[cfg(test)]
mod tests;

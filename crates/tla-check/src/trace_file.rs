// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Disk-based trace storage for large state space exploration.
//!
//! This module provides `TraceFile`, a disk-backed structure for storing
//! state trace information that enables counterexample reconstruction
//! for state spaces that exceed available RAM.
//!
//! # Design
//!
//! Inspired by TLC's TLCTrace, we store only (predecessor_offset, fingerprint)
//! pairs on disk rather than full states. To reconstruct a trace:
//!
//! 1. Walk backward from the error state's offset, collecting fingerprints
//! 2. Replay forward from the initial state, generating successors and
//!    matching by fingerprint until we reach the error state
//!
//! This trades CPU time (regenerating states) for memory efficiency.
//!
//! # File Format
//!
//! ```text
//! Record 0:
//!   predecessor_offset: u64 (8 bytes) - 0 for initial states
//!   fingerprint: u64 (8 bytes)
//! Record 1:
//!   predecessor_offset: u64 - file offset of predecessor record
//!   fingerprint: u64
//! ...
//! ```
//!
//! Each record is exactly 16 bytes. The file offset of a record
//! serves as its unique identifier.

use crate::state::{fp_hashmap, FpHashMap, Fingerprint};
use std::fs::{File, OpenOptions};
use std::io::{self, BufReader, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// Global counter for generating unique trace file names.
/// Combined with process ID to ensure uniqueness across concurrent tests.
static TRACE_FILE_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Sentinel value indicating no predecessor (initial state).
/// Using u64::MAX because 0 is a valid file offset (the first record).
const NO_PREDECESSOR: u64 = u64::MAX;

/// Size of each trace record in bytes.
const RECORD_SIZE: u64 = 16; // 8 bytes predecessor + 8 bytes fingerprint

/// Disk-based trace file for storing (predecessor, fingerprint) pairs.
///
/// This enables trace reconstruction for large state spaces without
/// keeping full states in memory.
///
/// # Thread Safety
///
/// This type is **not** thread-safe. For parallel model checking,
/// each worker should have its own `TraceFile` or use external
/// synchronization.
///
/// # Example
///
/// ```rust,no_run
/// use tla_check::TraceFile;
/// use tla_check::Fingerprint;
///
/// # fn main() -> std::io::Result<()> {
/// let mut trace = TraceFile::create("/tmp/trace.st")?;
///
/// // Record initial state
/// let init_loc = trace.write_initial(Fingerprint(12345))?;
///
/// // Record successor state with its predecessor
/// let succ_loc = trace.write_state(init_loc, Fingerprint(67890))?;
///
/// // Reconstruct fingerprint path from successor back to initial
/// let fps = trace.get_fingerprint_path(succ_loc)?;
/// assert_eq!(fps, vec![Fingerprint(12345), Fingerprint(67890)]);
/// # Ok(())
/// # }
/// ```
pub struct TraceFile {
    /// File path for the trace
    path: PathBuf,
    /// Writer for appending records (buffered)
    writer: BufWriter<File>,
    /// Current write position (next record offset)
    write_pos: u64,
    /// Whether to delete the file on drop (true for temp files)
    delete_on_drop: bool,
}

impl TraceFile {
    /// Decode a 16-byte on-disk record into `(predecessor_loc, fingerprint)`.
    fn decode_record(buf: [u8; 16]) -> (u64, Fingerprint) {
        let mut predecessor_bytes = [0u8; 8];
        predecessor_bytes.copy_from_slice(&buf[..8]);

        let mut fingerprint_bytes = [0u8; 8];
        fingerprint_bytes.copy_from_slice(&buf[8..]);

        (
            u64::from_le_bytes(predecessor_bytes),
            Fingerprint(u64::from_le_bytes(fingerprint_bytes)),
        )
    }

    /// Read and decode a single record at `loc`.
    fn read_record_at(reader: &mut BufReader<File>, loc: u64) -> io::Result<(u64, Fingerprint)> {
        reader.seek(SeekFrom::Start(loc))?;
        let mut buf = [0u8; 16];
        reader.read_exact(&mut buf)?;
        Ok(Self::decode_record(buf))
    }

    /// Create a new trace file, overwriting if it exists.
    ///
    /// # Arguments
    ///
    /// * `path` - Path to the trace file (typically with `.st` extension)
    ///
    /// # Returns
    ///
    /// Returns the new `TraceFile`, or an I/O error if file creation fails.
    pub fn create<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let path = path.as_ref().to_path_buf();
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(&path)?;

        Ok(TraceFile {
            path,
            // 64KB buffer reduces write syscalls by 8x vs default 8KB.
            // Each record is 16 bytes, so this holds 4096 records before flush.
            writer: BufWriter::with_capacity(64 * 1024, file),
            write_pos: 0,
            delete_on_drop: false,
        })
    }

    /// Create a trace file in a temporary location.
    ///
    /// The file is created in the system's temp directory with a unique name.
    /// Each call generates a distinct filename using a global counter to ensure
    /// concurrent tests/checkers don't share trace files.
    /// Use `path()` to get the actual file path.
    pub fn create_temp() -> io::Result<Self> {
        let temp_dir = std::env::temp_dir();
        let counter = TRACE_FILE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let filename = format!("tla2_trace_{}_{}.st", std::process::id(), counter);
        let mut trace = Self::create(temp_dir.join(filename))?;
        trace.delete_on_drop = true;
        Ok(trace)
    }

    /// Get the path to this trace file.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Write an initial state record (no predecessor).
    ///
    /// # Arguments
    ///
    /// * `fingerprint` - Fingerprint of the initial state
    ///
    /// # Returns
    ///
    /// Returns the file offset (location) of this record, which can be
    /// used as the `predecessor_loc` when writing successor states.
    pub fn write_initial(&mut self, fingerprint: Fingerprint) -> io::Result<u64> {
        self.write_record(NO_PREDECESSOR, fingerprint)
    }

    /// Write a state record with its predecessor.
    ///
    /// # Arguments
    ///
    /// * `predecessor_loc` - File offset of the predecessor state's record
    /// * `fingerprint` - Fingerprint of this state
    ///
    /// # Returns
    ///
    /// Returns the file offset (location) of this record.
    pub fn write_state(
        &mut self,
        predecessor_loc: u64,
        fingerprint: Fingerprint,
    ) -> io::Result<u64> {
        self.write_record(predecessor_loc, fingerprint)
    }

    /// Internal: write a single record and return its location.
    fn write_record(&mut self, predecessor_loc: u64, fingerprint: Fingerprint) -> io::Result<u64> {
        let loc = self.write_pos;

        // Write predecessor offset (8 bytes, little-endian)
        self.writer.write_all(&predecessor_loc.to_le_bytes())?;

        // Write fingerprint (8 bytes, little-endian)
        self.writer.write_all(&fingerprint.0.to_le_bytes())?;

        self.write_pos += RECORD_SIZE;

        Ok(loc)
    }

    /// Flush any buffered writes to disk.
    pub fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }

    /// Get the number of records written.
    pub fn record_count(&self) -> u64 {
        self.write_pos / RECORD_SIZE
    }

    /// Get the fingerprint path from an initial state to the given state.
    ///
    /// Walks backward from `end_loc` to an initial state, then reverses
    /// to return the path in forward order (initial -> end).
    ///
    /// # Arguments
    ///
    /// * `end_loc` - File offset of the end state's record
    ///
    /// # Returns
    ///
    /// Returns a vector of fingerprints from initial state to end state,
    /// or an I/O error if reading fails.
    pub fn get_fingerprint_path(&mut self, end_loc: u64) -> io::Result<Vec<Fingerprint>> {
        // Validate alignment: end_loc must be at a record boundary
        if end_loc % RECORD_SIZE != 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "trace file offset {} is not aligned to record size {}",
                    end_loc, RECORD_SIZE
                ),
            ));
        }

        // Flush writes first to ensure we can read them
        self.flush()?;

        // Open a separate reader for backward traversal
        let file = File::open(&self.path)?;
        let mut reader = BufReader::new(file);

        // Cycle detection: path length can never exceed total record count.
        // A longer path indicates corrupted predecessor pointers forming a cycle.
        let max_steps = self.record_count();

        let mut fps = Vec::new();
        let mut current_loc = end_loc;
        let mut steps: u64 = 0;

        loop {
            if steps > max_steps {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "cycle detected in trace file: walked {} steps but file contains only {} records",
                        steps, max_steps
                    ),
                ));
            }

            // Read record at current_loc.
            let (predecessor_loc, fp) = Self::read_record_at(&mut reader, current_loc)?;

            fps.push(fp);

            if predecessor_loc == NO_PREDECESSOR {
                // Reached initial state
                break;
            }

            // Validate predecessor alignment
            if predecessor_loc % RECORD_SIZE != 0 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "corrupted trace file: predecessor offset {} at record {} is not aligned to record size {}",
                        predecessor_loc, current_loc, RECORD_SIZE
                    ),
                ));
            }

            current_loc = predecessor_loc;
            steps += 1;
        }

        // Reverse to get initial -> end order
        fps.reverse();

        Ok(fps)
    }

    /// Read all records and return (fingerprint, file_offset) pairs.
    ///
    /// Part of #2881 Step 3: enables lazy trace index building. Instead of
    /// populating the fingerprint-to-offset index during BFS (one HashMap
    /// write per state), we build it on demand by scanning the trace file
    /// when trace reconstruction is needed. This eliminates the last
    /// per-state HashMap write on the BFS hot path.
    pub fn read_all_records(&mut self) -> io::Result<Vec<(Fingerprint, u64)>> {
        self.flush()?;

        let count = self.record_count() as usize;
        if count == 0 {
            return Ok(Vec::new());
        }

        let file = File::open(&self.path)?;
        let mut reader = BufReader::new(file);
        reader.seek(SeekFrom::Start(0))?;

        let mut result = Vec::with_capacity(count);
        let mut buf = [0u8; 16];
        let mut offset: u64 = 0;

        for _ in 0..count {
            reader.read_exact(&mut buf)?;
            let (_, fp) = Self::decode_record(buf);
            result.push((fp, offset));
            offset += RECORD_SIZE;
        }

        Ok(result)
    }

    /// Part of #3178: build child_fp→parent_fp map from all trace records (cold path).
    pub fn build_parents_map(
        &mut self,
    ) -> io::Result<std::collections::HashMap<Fingerprint, Fingerprint>> {
        self.flush()?;
        let count = self.record_count() as usize;
        if count == 0 {
            return Ok(std::collections::HashMap::new());
        }
        let file = File::open(&self.path)?;
        let mut reader = BufReader::new(file);
        reader.seek(SeekFrom::Start(0))?;
        let mut offset_to_fp = std::collections::HashMap::with_capacity(count);
        let mut records = Vec::with_capacity(count);
        let mut buf = [0u8; 16];
        let mut offset: u64 = 0;
        for _ in 0..count {
            reader.read_exact(&mut buf)?;
            let (pred, fp) = Self::decode_record(buf);
            offset_to_fp.insert(offset, fp);
            records.push((pred, fp));
            offset += RECORD_SIZE;
        }
        let mut parents = std::collections::HashMap::with_capacity(count);
        for &(pred, fp) in &records {
            if pred != NO_PREDECESSOR {
                if let Some(&parent_fp) = offset_to_fp.get(&pred) {
                    parents.insert(fp, parent_fp);
                }
            }
        }
        Ok(parents)
    }

    /// Part of #3178: write parent map into trace file (topological BFS order).
    pub fn restore_parents(
        &mut self,
        parents: &std::collections::HashMap<Fingerprint, Fingerprint>,
    ) -> io::Result<std::collections::HashMap<Fingerprint, u64>> {
        use std::collections::{HashMap, HashSet, VecDeque};
        if parents.is_empty() {
            return Ok(HashMap::new());
        }
        let children: HashSet<_> = parents.keys().copied().collect();
        let all_fps: HashSet<_> = children.iter().chain(parents.values()).copied().collect();
        let roots: Vec<_> = all_fps.difference(&children).copied().collect();
        let mut offset_map: HashMap<Fingerprint, u64> = HashMap::with_capacity(all_fps.len());
        for &fp in &roots {
            offset_map.insert(fp, self.write_initial(fp)?);
        }
        let mut children_of: HashMap<Fingerprint, Vec<Fingerprint>> = HashMap::new();
        for (&child, &parent) in parents {
            children_of.entry(parent).or_default().push(child);
        }
        let mut queue: VecDeque<_> = roots.into_iter().collect();
        while let Some(fp) = queue.pop_front() {
            if let Some(kids) = children_of.get(&fp) {
                let parent_loc = offset_map[&fp];
                for &child in kids {
                    offset_map.insert(child, self.write_state(parent_loc, child)?);
                    queue.push_back(child);
                }
            }
        }
        self.flush()?;
        Ok(offset_map)
    }

    /// Read a single record at the given location.
    ///
    /// # Arguments
    ///
    /// * `loc` - File offset of the record
    ///
    /// # Returns
    ///
    /// Returns (predecessor_loc, fingerprint), where predecessor_loc is 0
    /// for initial states.
    pub fn read_record(&mut self, loc: u64) -> io::Result<(u64, Fingerprint)> {
        self.flush()?;

        let file = File::open(&self.path)?;
        let mut reader = BufReader::new(file);
        Self::read_record_at(&mut reader, loc)
    }
}

impl Drop for TraceFile {
    fn drop(&mut self) {
        // Best-effort flush on drop
        let _ = self.flush();
        // Clean up temp files to avoid /tmp accumulation
        if self.delete_on_drop {
            let _ = std::fs::remove_file(&self.path);
        }
    }
}

/// Mapping from fingerprint to trace file location.
///
/// This is used during model checking to track where each state's
/// trace record is stored, enabling trace reconstruction.
#[derive(Debug, Default)]
pub struct TraceLocations {
    /// Map from fingerprint to file offset in the trace file (identity hasher).
    locations: FpHashMap<u64>,
}

impl TraceLocations {
    /// Create an empty location map.
    pub fn new() -> Self {
        TraceLocations {
            locations: fp_hashmap(),
        }
    }

    /// Record the location of a state in the trace file.
    pub fn insert(&mut self, fp: Fingerprint, loc: u64) {
        self.locations.insert(fp, loc);
    }

    /// Get the location of a state in the trace file.
    pub fn get(&self, fp: &Fingerprint) -> Option<u64> {
        self.locations.get(fp).copied()
    }

    /// Check if a fingerprint has a recorded location.
    pub fn contains(&self, fp: &Fingerprint) -> bool {
        self.locations.contains_key(fp)
    }

    /// Number of recorded locations.
    pub fn len(&self) -> usize {
        self.locations.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.locations.is_empty()
    }
}

#[cfg(test)]
#[path = "trace_file_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binary format read/write for checkpoint fingerprints, parent maps, and
//! depth maps.
//!
//! Each binary file has a fixed structure:
//! - 8-byte magic header (identifies file type)
//! - 8-byte little-endian entry count
//! - N entries of fixed width (8 bytes for fingerprints, 16 bytes for maps)
//!
//! All functions validate entry counts against both a hard safety limit
//! ([`MAX_BINARY_ENTRIES`]) and the actual file size to prevent OOM on
//! corrupted files.

use crate::state::{Fingerprint, State};
use std::collections::HashMap;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::Path;

use super::serializable::SerializableState;

/// Magic bytes identifying a TLA2 checkpoint fingerprint file
pub(super) const FINGERPRINT_MAGIC: &[u8; 8] = b"TLA2FP01";

/// Magic bytes identifying a TLA2 checkpoint parent map file
pub(super) const PARENTS_MAGIC: &[u8; 8] = b"TLA2PM01";

/// Magic bytes identifying a TLA2 checkpoint depths file
pub(super) const DEPTHS_MAGIC: &[u8; 8] = b"TLA2DP01";

/// Maximum entry count accepted when loading binary checkpoint files.
/// A corrupted length field exceeding this triggers a clean `InvalidData`
/// error instead of an OOM abort from `Vec::with_capacity`.
/// 4 billion entries ≈ 32 GB of fingerprints at 8 bytes each.
pub(super) const MAX_BINARY_ENTRIES: u64 = 4_000_000_000;

const BINARY_HEADER_BYTES: u64 = 16;
const FINGERPRINT_ENTRY_BYTES: u64 = 8;
const MAP_ENTRY_BYTES: u64 = 16;

/// Validate that a declared entry count is plausible given the file size.
pub(super) fn validate_binary_entry_len(
    len: u64,
    file_size: u64,
    entry_bytes: u64,
    label: &str,
) -> io::Result<usize> {
    if len > MAX_BINARY_ENTRIES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "{label} count {len} exceeds safety limit {MAX_BINARY_ENTRIES} \
                 — checkpoint file may be corrupted"
            ),
        ));
    }

    let payload_bytes = file_size.checked_sub(BINARY_HEADER_BYTES).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "{label} file is shorter than {BINARY_HEADER_BYTES}-byte header \
                 — checkpoint file may be corrupted"
            ),
        )
    })?;
    let max_entries_by_size = payload_bytes / entry_bytes;
    if len > max_entries_by_size {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "{label} count {len} exceeds payload capacity {max_entries_by_size} \
                 for file size {file_size} bytes — checkpoint file may be corrupted"
            ),
        ));
    }

    usize::try_from(len).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{label} count {len} does not fit in usize"),
        )
    })
}

// ============================================================================
// Fingerprints
// ============================================================================

/// Save fingerprints to a binary file.
pub(super) fn save_fingerprints(
    fingerprints: &[Fingerprint],
    path: impl AsRef<Path>,
) -> io::Result<()> {
    let mut file = BufWriter::new(std::fs::File::create(path)?);
    file.write_all(FINGERPRINT_MAGIC)?;
    file.write_all(&(fingerprints.len() as u64).to_le_bytes())?;
    for fp in fingerprints {
        file.write_all(&fp.0.to_le_bytes())?;
    }
    file.flush()?;
    file.get_ref().sync_all()?;
    Ok(())
}

/// Load fingerprints from a binary file.
pub(super) fn load_fingerprints(path: impl AsRef<Path>) -> io::Result<Vec<Fingerprint>> {
    let mut file = BufReader::new(std::fs::File::open(path)?);

    let mut magic = [0u8; 8];
    file.read_exact(&mut magic)?;
    if &magic != FINGERPRINT_MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid fingerprint file magic",
        ));
    }

    let mut len_bytes = [0u8; 8];
    file.read_exact(&mut len_bytes)?;
    let len = u64::from_le_bytes(len_bytes);
    let file_size = file.get_ref().metadata()?.len();
    let len = validate_binary_entry_len(len, file_size, FINGERPRINT_ENTRY_BYTES, "fingerprint")?;

    let mut fingerprints = Vec::with_capacity(len);
    for _ in 0..len {
        let mut fp_bytes = [0u8; 8];
        file.read_exact(&mut fp_bytes)?;
        fingerprints.push(Fingerprint(u64::from_le_bytes(fp_bytes)));
    }

    Ok(fingerprints)
}

// ============================================================================
// Frontier
// ============================================================================

/// Save frontier states to a JSON file.
pub(super) fn save_frontier(frontier: &[State], path: impl AsRef<Path>) -> io::Result<()> {
    let serializable: Vec<SerializableState> = frontier
        .iter()
        .map(SerializableState::from_state)
        .collect::<io::Result<_>>()?;
    let file = std::fs::File::create(path)?;
    let mut writer = BufWriter::new(file);
    serde_json::to_writer(&mut writer, &serializable)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e)))?;
    writer.flush()?;
    writer.get_ref().sync_all()?;
    Ok(())
}

/// Load frontier states from a JSON file.
pub(super) fn load_frontier(path: impl AsRef<Path>) -> io::Result<Vec<State>> {
    let file = std::fs::File::open(path)?;
    let serializable: Vec<SerializableState> = serde_json::from_reader(BufReader::new(file))
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e)))?;
    serializable
        .iter()
        .map(SerializableState::to_state)
        .collect()
}

// ============================================================================
// Parent map
// ============================================================================

/// Save parent pointers to a binary file.
pub(super) fn save_parents(
    parents: &HashMap<Fingerprint, Fingerprint>,
    path: impl AsRef<Path>,
) -> io::Result<()> {
    let mut file = BufWriter::new(std::fs::File::create(path)?);
    file.write_all(PARENTS_MAGIC)?;
    file.write_all(&(parents.len() as u64).to_le_bytes())?;
    for (child, parent) in parents {
        file.write_all(&child.0.to_le_bytes())?;
        file.write_all(&parent.0.to_le_bytes())?;
    }
    file.flush()?;
    file.get_ref().sync_all()?;
    Ok(())
}

/// Load parent pointers from a binary file.
pub(super) fn load_parents(
    path: impl AsRef<Path>,
) -> io::Result<HashMap<Fingerprint, Fingerprint>> {
    let mut file = BufReader::new(std::fs::File::open(path)?);

    let mut magic = [0u8; 8];
    file.read_exact(&mut magic)?;
    if &magic != PARENTS_MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid parents file magic",
        ));
    }

    let mut len_bytes = [0u8; 8];
    file.read_exact(&mut len_bytes)?;
    let len = u64::from_le_bytes(len_bytes);
    let file_size = file.get_ref().metadata()?.len();
    let len = validate_binary_entry_len(len, file_size, MAP_ENTRY_BYTES, "parent map")?;

    let mut parents = HashMap::with_capacity(len);
    for _ in 0..len {
        let mut child_bytes = [0u8; 8];
        let mut parent_bytes = [0u8; 8];
        file.read_exact(&mut child_bytes)?;
        file.read_exact(&mut parent_bytes)?;
        parents.insert(
            Fingerprint(u64::from_le_bytes(child_bytes)),
            Fingerprint(u64::from_le_bytes(parent_bytes)),
        );
    }

    Ok(parents)
}

// ============================================================================
// Depth map
// ============================================================================

/// Save depths to a binary file.
pub(super) fn save_depths(
    depths: &HashMap<Fingerprint, usize>,
    path: impl AsRef<Path>,
) -> io::Result<()> {
    let mut file = BufWriter::new(std::fs::File::create(path)?);
    file.write_all(DEPTHS_MAGIC)?;
    file.write_all(&(depths.len() as u64).to_le_bytes())?;
    for (fp, depth) in depths {
        file.write_all(&fp.0.to_le_bytes())?;
        file.write_all(&(*depth as u64).to_le_bytes())?;
    }
    file.flush()?;
    file.get_ref().sync_all()?;
    Ok(())
}

/// Load depths from a binary file.
pub(super) fn load_depths(path: impl AsRef<Path>) -> io::Result<HashMap<Fingerprint, usize>> {
    let mut file = BufReader::new(std::fs::File::open(path)?);

    let mut magic = [0u8; 8];
    file.read_exact(&mut magic)?;
    if &magic != DEPTHS_MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid depths file magic",
        ));
    }

    let mut len_bytes = [0u8; 8];
    file.read_exact(&mut len_bytes)?;
    let len = u64::from_le_bytes(len_bytes);
    let file_size = file.get_ref().metadata()?.len();
    let len = validate_binary_entry_len(len, file_size, MAP_ENTRY_BYTES, "depth map")?;

    let mut depths = HashMap::with_capacity(len);
    for _ in 0..len {
        let mut fp_bytes = [0u8; 8];
        let mut depth_bytes = [0u8; 8];
        file.read_exact(&mut fp_bytes)?;
        file.read_exact(&mut depth_bytes)?;
        depths.insert(
            Fingerprint(u64::from_le_bytes(fp_bytes)),
            u64::from_le_bytes(depth_bytes) as usize,
        );
    }

    Ok(depths)
}

// ============================================================================
// First violation
// ============================================================================

/// Load first_violation from JSON file, if present.
/// Returns Ok(None) if the file doesn't exist (backwards compatible with
/// checkpoints created before first_violation persistence).
pub(super) fn load_first_violation(
    path: impl AsRef<Path>,
) -> io::Result<Option<(String, Fingerprint)>> {
    let path = path.as_ref();
    if !path.exists() {
        return Ok(None);
    }
    let file = BufReader::new(std::fs::File::open(path)?);
    let data: serde_json::Value = serde_json::from_reader(file)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e)))?;
    let invariant = data["invariant"]
        .as_str()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing invariant field"))?
        .to_string();
    let fp_val = data["fingerprint"]
        .as_u64()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing fingerprint field"))?;
    Ok(Some((invariant, Fingerprint(fp_val))))
}

/// Load first action-property violation from JSON file, if present.
pub(super) fn load_first_action_property_violation(
    path: impl AsRef<Path>,
) -> io::Result<Option<(String, Fingerprint)>> {
    let path = path.as_ref();
    if !path.exists() {
        return Ok(None);
    }
    let file = BufReader::new(std::fs::File::open(path)?);
    let data: serde_json::Value = serde_json::from_reader(file)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("JSON error: {}", e)))?;
    let property = data["property"]
        .as_str()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing property field"))?
        .to_string();
    let fp_val = data["fingerprint"]
        .as_u64()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing fingerprint field"))?;
    Ok(Some((property, Fingerprint(fp_val))))
}

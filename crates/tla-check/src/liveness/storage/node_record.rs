// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! On-disk node record format for the disk-backed liveness graph.
//!
//! Each node record stores the complete topology for one behavior graph node:
//! the node's key `(state_fp, tableau_idx)`, parent pointer, BFS depth,
//! successor list, and precomputed check masks.
//!
//! Records are variable-length and designed for append-only writing to a
//! sequential file. The [`super::node_ptr_table::NodePtrTable`] (Slice C)
//! provides the `(fp, tidx) -> byte_offset` index for random reads.
//!
//! ## Record layout
//!
//! ```text
//! Header (64 bytes, all u64 for alignment):
//!   state_fp              u64
//!   tableau_idx           u64
//!   parent_fp             u64  (NO_PARENT sentinel if init node)
//!   parent_tidx           u64  (NO_PARENT sentinel if init node)
//!   depth                 u64
//!   succ_count            u64
//!   state_mask_words      u64
//!   action_mask_words     u64  (words per successor's action mask)
//!
//! Successor payload (succ_count * 16 bytes):
//!   [succ_fp: u64, succ_tidx: u64] * succ_count
//!
//! State check mask (state_mask_words * 8 bytes):
//!   [word: u64] * state_mask_words
//!
//! Action check masks (succ_count * action_mask_words * 8 bytes):
//!   [word: u64] * (succ_count * action_mask_words)
//! ```
//!
//! Part of #2732 Slice D.

use crate::liveness::behavior_graph::{BehaviorGraphNode, NodeInfo};
use crate::liveness::checker::CheckMask;
use crate::state::Fingerprint;
use std::io::{self, Read, Write};

/// Sentinel value for "no parent" in the parent_fp / parent_tidx fields.
const NO_PARENT: u64 = u64::MAX;

/// Fixed header size in bytes (8 fields × 8 bytes).
const HEADER_SIZE: usize = 64;

/// Bytes per successor entry (fp + tidx).
const SUCCESSOR_ENTRY_SIZE: usize = 16;

/// Write a node record to the given writer. Returns the number of bytes written.
pub(crate) fn write_node_record<W: Write>(
    w: &mut W,
    node: BehaviorGraphNode,
    info: &NodeInfo,
) -> io::Result<usize> {
    let succ_count = info.successors.len();
    let state_mask_words = info.state_check_mask.as_words().len();

    // Determine per-successor action mask word count.
    // Use the maximum word count across all action masks so shorter masks
    // are zero-padded to a uniform width.
    let action_mask_words = info
        .action_check_masks
        .iter()
        .map(|m| m.as_words().len())
        .max()
        .unwrap_or(0);

    // Header (64 bytes)
    let mut buf = [0u8; HEADER_SIZE];
    buf[0..8].copy_from_slice(&node.state_fp.0.to_le_bytes());
    buf[8..16].copy_from_slice(&(node.tableau_idx as u64).to_le_bytes());

    let (parent_fp, parent_tidx) = match info.parent {
        Some(p) => (p.state_fp.0, p.tableau_idx as u64),
        None => (NO_PARENT, NO_PARENT),
    };
    buf[16..24].copy_from_slice(&parent_fp.to_le_bytes());
    buf[24..32].copy_from_slice(&parent_tidx.to_le_bytes());
    buf[32..40].copy_from_slice(&(info.depth as u64).to_le_bytes());
    buf[40..48].copy_from_slice(&(succ_count as u64).to_le_bytes());
    buf[48..56].copy_from_slice(&(state_mask_words as u64).to_le_bytes());
    buf[56..64].copy_from_slice(&(action_mask_words as u64).to_le_bytes());
    w.write_all(&buf)?;

    let mut total = HEADER_SIZE;

    // Successor payload
    for succ in &info.successors {
        w.write_all(&succ.state_fp.0.to_le_bytes())?;
        w.write_all(&(succ.tableau_idx as u64).to_le_bytes())?;
        total += SUCCESSOR_ENTRY_SIZE;
    }

    // State check mask
    for &word in info.state_check_mask.as_words() {
        w.write_all(&word.to_le_bytes())?;
        total += 8;
    }

    // Action check masks (padded to uniform word count)
    for mask in &info.action_check_masks {
        let words = mask.as_words();
        for &word in words {
            w.write_all(&word.to_le_bytes())?;
        }
        // Pad with zeros if this mask has fewer words than the maximum.
        for _ in words.len()..action_mask_words {
            w.write_all(&0u64.to_le_bytes())?;
        }
        total += action_mask_words * 8;
    }

    Ok(total)
}

/// Read a u64 from a fixed-size subslice of a larger buffer.
///
/// The caller guarantees `offset + 8 <= buf.len()` (the buffer is always
/// `HEADER_SIZE` or `SUCCESSOR_ENTRY_SIZE` bytes, both multiples of 8).
#[inline]
fn read_u64(buf: &[u8], offset: usize) -> u64 {
    let bytes: [u8; 8] = buf[offset..offset + 8]
        .try_into()
        .expect("invariant: fixed-size record field is 8 bytes");
    u64::from_le_bytes(bytes)
}

/// Read a node record from the given reader.
/// Returns `(node_key, node_info)`.
pub(crate) fn read_node_record<R: Read>(r: &mut R) -> io::Result<(BehaviorGraphNode, NodeInfo)> {
    // Header
    let mut buf = [0u8; HEADER_SIZE];
    r.read_exact(&mut buf)?;

    let state_fp = Fingerprint(read_u64(&buf, 0));
    let tableau_idx = read_u64(&buf, 8) as usize;
    let parent_fp_raw = read_u64(&buf, 16);
    let parent_tidx_raw = read_u64(&buf, 24);
    let depth = read_u64(&buf, 32) as usize;
    let succ_count = read_u64(&buf, 40) as usize;
    let state_mask_words = read_u64(&buf, 48) as usize;
    let action_mask_words = read_u64(&buf, 56) as usize;

    let parent = if parent_fp_raw == NO_PARENT {
        None
    } else {
        Some(BehaviorGraphNode::new(
            Fingerprint(parent_fp_raw),
            parent_tidx_raw as usize,
        ))
    };

    // Successors
    let mut successors = Vec::with_capacity(succ_count);
    let mut entry_buf = [0u8; SUCCESSOR_ENTRY_SIZE];
    for _ in 0..succ_count {
        r.read_exact(&mut entry_buf)?;
        let succ_fp = Fingerprint(read_u64(&entry_buf, 0));
        let succ_tidx = read_u64(&entry_buf, 8) as usize;
        successors.push(BehaviorGraphNode::new(succ_fp, succ_tidx));
    }

    // State check mask
    let state_check_mask = read_check_mask(r, state_mask_words)?;

    // Action check masks
    let mut action_check_masks = Vec::with_capacity(succ_count);
    for _ in 0..succ_count {
        action_check_masks.push(read_check_mask(r, action_mask_words)?);
    }

    let node = BehaviorGraphNode::new(state_fp, tableau_idx);
    let info = NodeInfo {
        successors,
        parent,
        depth,
        state_check_mask,
        action_check_masks,
    };
    Ok((node, info))
}

/// Read a CheckMask of `word_count` u64 words.
fn read_check_mask<R: Read>(r: &mut R, word_count: usize) -> io::Result<CheckMask> {
    if word_count == 0 {
        return Ok(CheckMask::new());
    }
    let mut words = Vec::with_capacity(word_count);
    let mut buf = [0u8; 8];
    for _ in 0..word_count {
        r.read_exact(&mut buf)?;
        words.push(u64::from_le_bytes(buf));
    }
    Ok(CheckMask::from_words(words))
}

/// Compute the total byte size of a node record without writing it.
#[cfg(test)]
pub(crate) fn record_byte_size(info: &NodeInfo) -> usize {
    let succ_count = info.successors.len();
    let state_mask_words = info.state_check_mask.as_words().len();
    let action_mask_words = info
        .action_check_masks
        .iter()
        .map(|m| m.as_words().len())
        .max()
        .unwrap_or(0);

    HEADER_SIZE
        + succ_count * SUCCESSOR_ENTRY_SIZE
        + state_mask_words * 8
        + succ_count * action_mask_words * 8
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn make_node(fp: u64, tidx: usize) -> BehaviorGraphNode {
        BehaviorGraphNode::new(Fingerprint(fp), tidx)
    }

    fn make_info(
        successors: Vec<BehaviorGraphNode>,
        parent: Option<BehaviorGraphNode>,
        depth: usize,
    ) -> NodeInfo {
        NodeInfo {
            successors,
            parent,
            depth,
            state_check_mask: CheckMask::new(),
            action_check_masks: Vec::new(),
        }
    }

    #[test]
    fn test_roundtrip_init_node_no_successors() {
        let node = make_node(42, 0);
        let info = make_info(vec![], None, 0);

        let mut buf = Vec::new();
        let written = write_node_record(&mut buf, node, &info).unwrap();
        assert_eq!(written, HEADER_SIZE);
        assert_eq!(buf.len(), HEADER_SIZE);

        let mut cursor = Cursor::new(&buf);
        let (read_node, read_info) = read_node_record(&mut cursor).unwrap();
        assert_eq!(read_node, node);
        assert_eq!(read_info.parent, None);
        assert_eq!(read_info.depth, 0);
        assert!(read_info.successors.is_empty());
    }

    #[test]
    fn test_roundtrip_with_successors() {
        let node = make_node(100, 1);
        let parent = make_node(50, 0);
        let succ_a = make_node(200, 2);
        let succ_b = make_node(300, 0);
        let info = make_info(vec![succ_a, succ_b], Some(parent), 3);

        let mut buf = Vec::new();
        let written = write_node_record(&mut buf, node, &info).unwrap();
        let expected_size = HEADER_SIZE + 2 * SUCCESSOR_ENTRY_SIZE;
        assert_eq!(written, expected_size);

        let mut cursor = Cursor::new(&buf);
        let (read_node, read_info) = read_node_record(&mut cursor).unwrap();
        assert_eq!(read_node, node);
        assert_eq!(read_info.parent, Some(parent));
        assert_eq!(read_info.depth, 3);
        assert_eq!(read_info.successors.len(), 2);
        assert_eq!(read_info.successors[0], succ_a);
        assert_eq!(read_info.successors[1], succ_b);
    }

    #[test]
    fn test_roundtrip_with_check_masks() {
        let node = make_node(42, 0);
        let succ = make_node(99, 1);

        let mut state_mask = CheckMask::new();
        state_mask.set(0);
        state_mask.set(5);
        state_mask.set(63);

        let mut action_mask = CheckMask::new();
        action_mask.set(1);
        action_mask.set(7);

        let info = NodeInfo {
            successors: vec![succ],
            parent: None,
            depth: 0,
            state_check_mask: state_mask.clone(),
            action_check_masks: vec![action_mask.clone()],
        };

        let mut buf = Vec::new();
        write_node_record(&mut buf, node, &info).unwrap();

        let mut cursor = Cursor::new(&buf);
        let (_, read_info) = read_node_record(&mut cursor).unwrap();

        assert!(read_info.state_check_mask.get(0));
        assert!(read_info.state_check_mask.get(5));
        assert!(read_info.state_check_mask.get(63));
        assert!(!read_info.state_check_mask.get(1));

        assert_eq!(read_info.action_check_masks.len(), 1);
        assert!(read_info.action_check_masks[0].get(1));
        assert!(read_info.action_check_masks[0].get(7));
        assert!(!read_info.action_check_masks[0].get(0));
    }

    #[test]
    fn test_roundtrip_multi_word_masks() {
        let node = make_node(42, 0);
        let succ = make_node(99, 1);

        let mut state_mask = CheckMask::new();
        state_mask.set(0);
        state_mask.set(65); // forces second word
        state_mask.set(130); // forces third word

        let mut action_mask = CheckMask::new();
        action_mask.set(64);
        action_mask.set(128);

        let info = NodeInfo {
            successors: vec![succ],
            parent: None,
            depth: 0,
            state_check_mask: state_mask,
            action_check_masks: vec![action_mask],
        };

        let mut buf = Vec::new();
        write_node_record(&mut buf, node, &info).unwrap();

        let mut cursor = Cursor::new(&buf);
        let (_, read_info) = read_node_record(&mut cursor).unwrap();

        assert!(read_info.state_check_mask.get(0));
        assert!(read_info.state_check_mask.get(65));
        assert!(read_info.state_check_mask.get(130));
        assert!(!read_info.state_check_mask.get(1));
        assert!(!read_info.state_check_mask.get(64));

        assert!(read_info.action_check_masks[0].get(64));
        assert!(read_info.action_check_masks[0].get(128));
    }

    #[test]
    fn test_roundtrip_multiple_successors_with_masks() {
        let node = make_node(10, 0);
        let succs = vec![make_node(20, 1), make_node(30, 2), make_node(40, 0)];

        let mut state_mask = CheckMask::new();
        state_mask.set(3);

        let action_masks: Vec<CheckMask> = (0..3)
            .map(|i| {
                let mut m = CheckMask::new();
                m.set(i * 2);
                m
            })
            .collect();

        let info = NodeInfo {
            successors: succs.clone(),
            parent: Some(make_node(1, 0)),
            depth: 5,
            state_check_mask: state_mask,
            action_check_masks: action_masks,
        };

        let mut buf = Vec::new();
        write_node_record(&mut buf, node, &info).unwrap();

        let mut cursor = Cursor::new(&buf);
        let (read_node, read_info) = read_node_record(&mut cursor).unwrap();

        assert_eq!(read_node, node);
        assert_eq!(read_info.successors, succs);
        assert_eq!(read_info.depth, 5);
        assert!(read_info.state_check_mask.get(3));

        for i in 0..3 {
            assert!(read_info.action_check_masks[i].get(i * 2));
        }
    }

    #[test]
    fn test_multiple_records_sequential() {
        let mut buf = Vec::new();
        let mut offsets = Vec::new();

        // Write three records sequentially.
        for i in 0..3 {
            let offset = buf.len();
            offsets.push(offset);
            let node = make_node(100 + i as u64, i);
            let info = make_info(
                vec![make_node(200 + i as u64, 0)],
                if i > 0 {
                    Some(make_node(100 + (i - 1) as u64, i - 1))
                } else {
                    None
                },
                i,
            );
            write_node_record(&mut buf, node, &info).unwrap();
        }

        // Read each record back by seeking to its offset.
        for i in 0..3 {
            let mut cursor = Cursor::new(&buf[offsets[i]..]);
            let (read_node, read_info) = read_node_record(&mut cursor).unwrap();
            assert_eq!(read_node, make_node(100 + i as u64, i));
            assert_eq!(read_info.depth, i);
            assert_eq!(read_info.successors.len(), 1);
        }
    }

    #[test]
    fn test_record_byte_size() {
        let info = make_info(vec![], None, 0);
        assert_eq!(record_byte_size(&info), HEADER_SIZE);

        let info2 = make_info(vec![make_node(1, 0), make_node(2, 1)], None, 0);
        assert_eq!(
            record_byte_size(&info2),
            HEADER_SIZE + 2 * SUCCESSOR_ENTRY_SIZE
        );

        // With masks.
        let mut state_mask = CheckMask::new();
        state_mask.set(0);
        let mut action_mask = CheckMask::new();
        action_mask.set(1);
        let info3 = NodeInfo {
            successors: vec![make_node(1, 0)],
            parent: None,
            depth: 0,
            state_check_mask: state_mask,
            action_check_masks: vec![action_mask],
        };
        // header + 1 succ * 16 + 1 state word * 8 + 1 succ * 1 action word * 8
        assert_eq!(record_byte_size(&info3), HEADER_SIZE + 16 + 8 + 8);
    }

    #[test]
    fn test_written_size_matches_computed() {
        let node = make_node(42, 3);
        let mut state_mask = CheckMask::new();
        state_mask.set(10);
        state_mask.set(70);
        let mut am0 = CheckMask::new();
        am0.set(5);
        let mut am1 = CheckMask::new();
        am1.set(100);

        let info = NodeInfo {
            successors: vec![make_node(1, 0), make_node(2, 1)],
            parent: Some(make_node(10, 0)),
            depth: 7,
            state_check_mask: state_mask,
            action_check_masks: vec![am0, am1],
        };

        let mut buf = Vec::new();
        let written = write_node_record(&mut buf, node, &info).unwrap();
        assert_eq!(written, buf.len());
        assert_eq!(record_byte_size(&info), written);
    }
}

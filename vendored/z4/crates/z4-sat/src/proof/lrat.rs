// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT proof writer for generating UNSAT certificates with clause IDs and hints.
//!
//! # Hint type boundary: `u64` vs `i64` (#5634)
//!
//! The LRAT *format* uses **signed** hint IDs: positive values are clause-ID
//! references for RUP checking, and negative values mark RAT witness boundaries
//! (see `z4-lrat-check::lrat_parser` for the format specification).
//!
//! This writer uses **unsigned** `u64` hints because Z4 currently only generates
//! RUP proofs — all hints are positive clause-ID references. A `debug_assert!`
//! in [`LratWriter::add`] verifies that no hint exceeds `i64::MAX`, ensuring
//! round-trip safety with the signed `i64` checker.
//!
//! **If Z4 adds RAT proof generation** (e.g., for blocked clause elimination),
//! this API must change to `&[i64]` to support negative RAT witness markers.
//! All downstream callers (`ProofOutput::add`, `ProofManager::emit_add`,
//! `proof_emit_add`, `proof_emit_add_prechecked`) will need corresponding
//! signature changes. Internal hint storage (`ClauseTraceEntry::resolution_hints`)
//! may remain `Vec<u64>` since resolution hints are always positive — the
//! conversion to `i64` should happen at the proof-writing boundary.

use super::{has_duplicate_literal, ToDimacs};
use crate::literal::Literal;
use std::io::{self, Write};

/// LRAT proof writer for generating UNSAT certificates with clause IDs and hints
///
/// LRAT proofs include clause IDs and resolution hints, enabling linear-time
/// proof checking. Each added clause includes:
/// - A unique clause ID
/// - The clause literals
/// - Hint IDs (clause IDs used to derive this clause)
///
/// Like `DratWriter`, tracks I/O errors internally (CaDiCaL-style).
pub struct LratWriter<W: Write> {
    writer: W,
    binary: bool,
    /// Number of original (input) clauses; immutable after construction.
    num_original: u64,
    /// Next clause ID to assign
    next_id: u64,
    /// ID of the most recently added clause (for deletion batching)
    latest_id: u64,
    /// Pending deletions (batched for efficiency)
    pending_deletions: Vec<u64>,
    /// Count of clauses successfully added (does not count failed writes)
    added_count: u64,
    /// Count of clauses deleted (batched; actual I/O failure caught on flush)
    deleted_count: u64,
    /// Set on first I/O error; subsequent writes become no-ops
    io_failed: bool,
}

impl<W: Write> LratWriter<W> {
    /// Create a new LRAT writer with text format
    ///
    /// `num_original_clauses` is the number of clauses in the original formula.
    /// The first learned clause will get ID `num_original_clauses + 1`.
    pub fn new_text(writer: W, num_original_clauses: u64) -> Self {
        Self {
            writer,
            binary: false,
            num_original: num_original_clauses,
            next_id: num_original_clauses + 1,
            latest_id: num_original_clauses,
            pending_deletions: Vec::new(),
            added_count: 0,
            deleted_count: 0,
            io_failed: false,
        }
    }

    /// Create a new LRAT writer with binary format
    ///
    /// `num_original_clauses` is the number of clauses in the original formula.
    pub fn new_binary(writer: W, num_original_clauses: u64) -> Self {
        Self {
            writer,
            binary: true,
            num_original: num_original_clauses,
            next_id: num_original_clauses + 1,
            latest_id: num_original_clauses,
            pending_deletions: Vec::new(),
            added_count: 0,
            deleted_count: 0,
            io_failed: false,
        }
    }

    /// Flush any pending deletions to the output
    fn flush_deletions(&mut self) -> io::Result<()> {
        if self.pending_deletions.is_empty() {
            return Ok(());
        }

        if self.binary {
            self.writer.write_all(b"d")?;
            // Take the pending deletions to avoid borrow conflict
            let deletions = std::mem::take(&mut self.pending_deletions);
            for id in &deletions {
                self.write_binary_id(*id)?;
            }
            self.writer.write_all(&[0])?;
        } else {
            // Text format: "step_id d id1 id2 ... 0"
            // Step IDs must be strictly increasing (both additions AND deletions
            // share the same monotonic ID space). Using latest_id reuses the
            // previous addition's ID, which is a format error (#4398).
            let del_id = self.next_id;
            self.next_id = del_id + 1;
            write!(self.writer, "{del_id} d ")?;
            for &id in &self.pending_deletions {
                write!(self.writer, "{id} ")?;
            }
            writeln!(self.writer, "0")?;
            self.pending_deletions.clear();
        }

        Ok(())
    }

    /// Log addition of a learned clause with resolution hints.
    ///
    /// Returns the assigned clause ID. After an I/O failure, subsequent calls
    /// are no-ops returning `Ok(0)` (CaDiCaL-style). Counter only increments
    /// on successful writes.
    ///
    /// # Hint type boundary (`u64` vs `i64`)
    ///
    /// The writer uses unsigned `u64` hints because Z4 currently only generates
    /// RUP proofs (all hints are positive clause-ID references). The LRAT
    /// *format* uses signed hint IDs — negative values mark RAT witness
    /// boundaries (see `z4-lrat-check` parser). If Z4 adds RAT proof
    /// generation in the future, this API must change to `&[i64]` (#5634).
    pub fn add(&mut self, clause: &[Literal], hints: &[u64]) -> io::Result<u64> {
        debug_assert!(
            !has_duplicate_literal(clause),
            "BUG: LRAT add contains duplicate literal in clause of length {}",
            clause.len()
        );
        // Note: empty hints are valid for original/axiom clauses written to the
        // LRAT proof (TrustedTransform additions from inprocessing). These are
        // treated as axioms in the LRAT checker and don't need resolution chains.
        // The ProofManager validates Derived hints at a higher level (#4490, #7108).
        debug_assert!(
            hints.iter().all(|&h| h != 0),
            "BUG: LRAT hint contains ID 0 -- hint IDs must be valid clause references",
        );
        // RUP-only guard: all hints must fit in i64 for LRAT format compatibility.
        // This will be removed when the writer switches to i64 hints for RAT support (#5634).
        debug_assert!(
            hints.iter().all(|&h| i64::try_from(h).is_ok()),
            "BUG: LRAT hint exceeds i64::MAX -- would corrupt signed LRAT format",
        );
        // Note: hint range validation (h < next_id) is done in ProofManager::validate_lrat_hints
        // which has access to the full set of registered clause IDs. The LratWriter does not
        // track externally registered IDs (from Solver::add_clause), so range checks here
        // would produce false positives.
        if self.io_failed {
            return Ok(0);
        }
        // Flush any pending deletions first
        if let Err(e) = self.flush_deletions() {
            self.io_failed = true;
            return Err(e);
        }

        let id = self.next_id;
        let result = if self.binary {
            self.write_binary_add(id, clause, hints)
        } else {
            self.write_text_add(id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.next_id = id + 1;
                self.latest_id = id;
                self.added_count += 1;
                Ok(id)
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Write an addition with a pre-assigned clause ID (#8105).
    ///
    /// Used by backward reconstruction: the ID was reserved during solving
    /// via `reserve_id`, and now the addition line is written with proper hints.
    /// Does NOT advance `next_id` or `added_count` since the ID was already
    /// reserved and counted.
    pub fn add_with_id(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        hints: &[u64],
    ) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        // Flush pending deletions before writing the addition.
        if let Err(e) = self.flush_deletions() {
            self.io_failed = true;
            return Err(e);
        }
        let result = if self.binary {
            self.write_binary_add(clause_id, clause, hints)
        } else {
            self.write_text_add(clause_id, clause, hints)
        };
        match result {
            Ok(()) => {
                self.added_count += 1;
                Ok(())
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Write addition in text format: "id lit1 lit2 ... 0 hint1 hint2 ... 0"
    fn write_text_add(&mut self, id: u64, clause: &[Literal], hints: &[u64]) -> io::Result<()> {
        write!(self.writer, "{id} ")?;
        for lit in clause {
            write!(self.writer, "{} ", lit.to_dimacs())?;
        }
        write!(self.writer, "0 ")?;
        for &hint in hints {
            write!(self.writer, "{hint} ")?;
        }
        writeln!(self.writer, "0")
    }

    /// Write addition in binary format
    fn write_binary_add(&mut self, id: u64, clause: &[Literal], hints: &[u64]) -> io::Result<()> {
        self.writer.write_all(b"a")?;
        self.write_binary_id(id)?;
        for lit in clause {
            self.write_binary_lit(*lit)?;
        }
        self.writer.write_all(&[0])?;
        for &hint in hints {
            self.write_binary_id(hint)?;
        }
        self.writer.write_all(&[0])
    }

    /// Log deletion of a clause by ID
    ///
    /// Deletions are batched for efficiency and flushed on the next add.
    /// After an I/O failure, subsequent calls are no-ops.
    pub fn delete(&mut self, clause_id: u64) -> io::Result<()> {
        // Clause ID 0 is a reserved sentinel and never a valid clause reference.
        // The full ID-references-known-clause check is done by ProofManager::emit_delete()
        // which has visibility into both original and derived clause IDs.
        debug_assert!(
            clause_id != 0,
            "BUG: LRAT delete of clause ID 0 (reserved sentinel)"
        );
        debug_assert!(
            clause_id < self.next_id,
            "BUG: LRAT delete of future clause ID {clause_id} (next_id={})",
            self.next_id,
        );
        if self.io_failed {
            return Ok(());
        }
        self.deleted_count += 1;
        self.pending_deletions.push(clause_id);
        Ok(())
    }

    /// Write a literal in binary encoding (same logic as `DratWriter`).
    ///
    /// Uses checked arithmetic to prevent silent overflow (#4474).
    fn write_binary_lit(&mut self, lit: Literal) -> io::Result<()> {
        let var = lit
            .variable()
            .0
            .checked_add(1) // 1-indexed
            .expect("BUG: variable index overflow in binary LRAT encoding");
        let encoded = var
            .checked_mul(2)
            .expect("BUG: literal encoding overflow in binary LRAT encoding")
            + u32::from(!lit.is_positive()); // +0 or +1; safe since 2*var is even

        let mut val = encoded;
        while val > 127 {
            self.writer.write_all(&[(val as u8 & 0x7f) | 0x80])?;
            val >>= 7;
        }
        self.writer.write_all(&[val as u8])
    }

    /// Write a clause ID in binary encoding (variable-length).
    ///
    /// Binary LRAT encodes all values (IDs, literals, hints) as
    /// `2 * abs(val) + sign_bit` in LEB128. IDs are always positive,
    /// so: `val = 2 * id`.
    ///
    /// Reference: CaDiCaL `lrattracer.cpp:56-68`, drat-trim `decompress.c:34-46`.
    fn write_binary_id(&mut self, id: u64) -> io::Result<()> {
        let mut val = id
            .checked_mul(2)
            .expect("BUG: clause ID overflow in binary LRAT encoding");
        while val > 127 {
            self.writer.write_all(&[(val as u8 & 0x7f) | 0x80])?;
            val >>= 7;
        }
        self.writer.write_all(&[val as u8])
    }

    /// Get the next clause ID that will be assigned
    pub fn next_id(&self) -> u64 {
        self.next_id
    }

    /// Advance the ID counter without emitting a proof step.
    ///
    /// Used by the fail-close mechanism (#4713): when a theory-lemma write is
    /// suppressed, the solver still allocates a clause ID. Calling this keeps
    /// the writer's counter synchronized so subsequent writes (e.g., the empty
    /// clause) receive non-conflicting IDs.
    pub fn reserve_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Advance the ID counter so it is at least `min_next`.
    ///
    /// Used to synchronize the writer's counter after axiom IDs are allocated
    /// through a separate path (e.g., `register_lrat_axiom` via `next_lrat_id`
    /// in ProofManager). No-op if the counter is already >= `min_next`.
    pub fn advance_past(&mut self, min_next: u64) {
        if min_next > self.next_id {
            self.next_id = min_next;
        }
    }

    /// Get the number of original clauses
    pub fn num_original_clauses(&self) -> u64 {
        self.num_original
    }

    /// Get the number of clauses successfully added
    pub fn added_count(&self) -> u64 {
        self.added_count
    }

    /// Get the number of clauses deleted
    pub fn deleted_count(&self) -> u64 {
        self.deleted_count
    }

    /// Returns true if any I/O error occurred during proof writing
    pub fn has_io_error(&self) -> bool {
        self.io_failed
    }

    /// Flush the writer (including any pending deletions; no-op after I/O failure)
    pub fn flush(&mut self) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        if let Err(e) = self.flush_deletions() {
            self.io_failed = true;
            return Err(e);
        }
        match self.writer.flush() {
            Ok(()) => Ok(()),
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Finalize the proof by flushing pending deletions and returning the inner writer
    ///
    /// Returns an error if an I/O failure occurred during proof writing.
    pub fn into_inner(mut self) -> io::Result<W> {
        if self.io_failed {
            return Err(io::Error::other(
                "LRAT proof writer encountered I/O error during solve",
            ));
        }
        self.flush_deletions()?;
        Ok(self.writer)
    }
}

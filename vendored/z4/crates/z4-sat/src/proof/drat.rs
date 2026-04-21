// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DRAT proof writer for generating UNSAT certificates.

use super::{has_duplicate_literal, ToDimacs};
use crate::literal::Literal;
use std::io::{self, Write};

/// DRAT proof writer for generating UNSAT certificates
///
/// Tracks I/O errors internally (CaDiCaL-style): on first write failure,
/// `io_failed` is set and all subsequent writes become no-ops. Callers can
/// check `has_io_error()` at proof finalization to detect truncated proofs.
pub struct DratWriter<W: Write> {
    writer: W,
    binary: bool,
    /// Count of clauses successfully added (does not count failed writes)
    added_count: u64,
    /// Count of clauses successfully deleted (does not count failed writes)
    deleted_count: u64,
    /// Set on first I/O error; subsequent writes become no-ops
    io_failed: bool,
}

impl<W: Write> DratWriter<W> {
    /// Create a new DRAT writer with text format
    pub fn new_text(writer: W) -> Self {
        Self {
            writer,
            binary: false,
            added_count: 0,
            deleted_count: 0,
            io_failed: false,
        }
    }

    /// Create a new DRAT writer with binary format
    pub fn new_binary(writer: W) -> Self {
        Self {
            writer,
            binary: true,
            added_count: 0,
            deleted_count: 0,
            io_failed: false,
        }
    }

    /// Log addition of a learned clause
    ///
    /// After an I/O failure, subsequent calls are no-ops (CaDiCaL-style).
    /// The counter only increments on successful writes.
    pub fn add(&mut self, clause: &[Literal]) -> io::Result<()> {
        debug_assert!(
            !has_duplicate_literal(clause),
            "BUG: DRAT add contains duplicate literal in clause of length {}",
            clause.len()
        );
        if self.io_failed {
            return Ok(());
        }
        let result = if self.binary {
            self.write_binary_clause(clause, false)
        } else {
            self.write_text_clause(clause, false)
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

    /// Log deletion of a clause
    ///
    /// After an I/O failure, subsequent calls are no-ops (CaDiCaL-style).
    /// The counter only increments on successful writes.
    pub fn delete(&mut self, clause: &[Literal]) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        let result = if self.binary {
            self.write_binary_clause(clause, true)
        } else {
            self.write_text_clause(clause, true)
        };
        match result {
            Ok(()) => {
                self.deleted_count += 1;
                Ok(())
            }
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Write clause in text format
    fn write_text_clause(&mut self, clause: &[Literal], is_delete: bool) -> io::Result<()> {
        if is_delete {
            write!(self.writer, "d ")?;
        }
        for lit in clause {
            write!(self.writer, "{} ", lit.to_dimacs())?;
        }
        writeln!(self.writer, "0")
    }

    /// Write clause in binary format
    fn write_binary_clause(&mut self, clause: &[Literal], is_delete: bool) -> io::Result<()> {
        // Write marker byte
        self.writer
            .write_all(&[if is_delete { b'd' } else { b'a' }])?;

        // Write each literal in binary encoding
        for lit in clause {
            self.write_binary_lit(*lit)?;
        }

        // Write terminating 0
        self.writer.write_all(&[0])
    }

    /// Write a literal in binary (variable-length) encoding
    ///
    /// Binary literal encoding: positive lit v -> 2*(v+1), negative -> 2*(v+1)+1
    /// Then encoded as variable-length integer (LEB128-style).
    ///
    /// Uses checked arithmetic to prevent silent overflow for large variable
    /// indices (see #4474).
    fn write_binary_lit(&mut self, lit: Literal) -> io::Result<()> {
        let var = lit
            .variable()
            .0
            .checked_add(1) // 1-indexed
            .expect("BUG: variable index overflow in binary DRAT encoding");
        let encoded = var
            .checked_mul(2)
            .expect("BUG: literal encoding overflow in binary DRAT encoding")
            + u32::from(!lit.is_positive()); // +0 or +1; safe since 2*var is even

        // Variable-length encoding (similar to LEB128)
        let mut val = encoded;
        while val > 127 {
            self.writer.write_all(&[(val as u8 & 0x7f) | 0x80])?;
            val >>= 7;
        }
        self.writer.write_all(&[val as u8])
    }

    /// Get the number of clauses successfully added
    pub fn added_count(&self) -> u64 {
        self.added_count
    }

    /// Get the number of clauses successfully deleted
    pub fn deleted_count(&self) -> u64 {
        self.deleted_count
    }

    /// Returns true if any I/O error occurred during proof writing
    pub fn has_io_error(&self) -> bool {
        self.io_failed
    }

    /// Flush the writer (no-op after I/O failure)
    pub fn flush(&mut self) -> io::Result<()> {
        if self.io_failed {
            return Ok(());
        }
        match self.writer.flush() {
            Ok(()) => Ok(()),
            Err(e) => {
                self.io_failed = true;
                Err(e)
            }
        }
    }

    /// Get the inner writer back
    ///
    /// Returns an error if an I/O failure occurred during proof writing,
    /// indicating the proof stream is truncated/corrupted.
    pub fn into_inner(self) -> io::Result<W> {
        if self.io_failed {
            return Err(io::Error::other(
                "DRAT proof writer encountered I/O error during solve",
            ));
        }
        Ok(self.writer)
    }
}

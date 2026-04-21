// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof writer accessors.
//!
//! The bulk of result declaration logic is in sibling modules:
//! - `finalize_unsat`: UNSAT declaration and proof finalization
//! - `finalize_sat`: SAT model reconstruction, verification, and result shaping
//! - `ext_conflict`: Extension/theory conflict postprocessing

use super::super::*;

impl Solver {
    /// Get the proof writer (for testing/inspection)
    pub fn proof_writer(&self) -> Option<&ProofOutput> {
        self.proof_manager.as_ref().map(ProofManager::output)
    }

    /// Take the proof writer out of the solver (consumes proof logging capability)
    pub fn take_proof_writer(&mut self) -> Option<ProofOutput> {
        self.proof_manager.take().map(ProofManager::into_output)
    }
}

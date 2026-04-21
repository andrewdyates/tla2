// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the EUF theory solver.

use crate::solver::EufSolver;
use crate::types::{CongruenceTable, ENode};
use proptest::prelude::*;
use serial_test::serial;
use z4_core::term::{Symbol, TermId, TermStore};
use z4_core::{
    assert_conflict_soundness, DiscoveredEquality, Sort, TheoryLit, TheoryResult, TheorySolver,
};

mod congruence;
mod disequality;
mod infrastructure;
mod soundness;

fn has_discovered_equality(equalities: &[DiscoveredEquality], a: TermId, b: TermId) -> bool {
    equalities
        .iter()
        .any(|e| (e.lhs == a && e.rhs == b) || (e.lhs == b && e.rhs == a))
}

fn new_incremental_euf(store: &TermStore) -> EufSolver<'_> {
    EufSolver::new(store)
}

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test hub for `model.rs` — split into focused shards by concern.
//!
//! - `fixtures`: shared PNML constants, XML writers, helper functions
//! - `load`: model loading and dispatch smoke tests
//! - `aliases`: alias resolution unit checks
//! - `neo_election_ground_truth`: authoritative ground-truth regressions
//! - `neo_election_diagnostics`: RF-10 reduction diagnostics and soundness
//! - `neo_election_parity`: COL/PT structural and execution parity

use super::*;
use crate::examination::{collect_examination_core, Examination, ExaminationValue, Verdict};
use crate::explorer::ExplorationConfig;
use crate::petri_net::{PlaceIdx, TransitionIdx};
use crate::property_xml::Formula;

mod fixtures;

mod aliases;
mod load;
mod neo_election_diagnostics;
mod neo_election_ground_truth;
mod neo_election_parity;

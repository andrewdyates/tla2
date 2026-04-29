// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the unified BFS worker loop (`run_bfs_worker`).
//!
//! Extracted from `worker_loop.rs` as part of #3644.
//! Split into child modules as part of #3664.

use super::{run_bfs_worker, BfsLoopOutcome};
use crate::check::model_checker::bfs::transport::BfsWorkerConfig;

mod control_flow;
mod fixtures;
mod profile_termination;

use fixtures::{ConfigurableMock, MockTransport};

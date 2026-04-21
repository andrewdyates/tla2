// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for parallel BFS transport.
//! Split from monolithic tests.rs (1085 LOC) for maintainability.

mod helpers;

mod construction;
mod dequeue;
mod routing;
mod shared_frontier;
mod streaming;

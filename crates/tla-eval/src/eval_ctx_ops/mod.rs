// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EvalCtx operational methods: mutation, registration, lookup, field accessors,
//! scope guards, and shared-ctx accessors. Part of #2764 / #1643.
//!
//! Split into child modules by operation category (#3442):
//! - `mutation`: Context mutation, state-switch constructors, action context cache
//! - `registration`: Operator/variable registration, config mutation
//! - `accessors`: Field accessors, shared-ctx delegates, scope guards
//! - `lookup`: Variable lookup, operator lookup

mod accessors;
mod lookup;
mod mutation;
mod registration;

pub use mutation::clear_action_ctx_cache;

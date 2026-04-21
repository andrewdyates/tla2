// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani formal verification harnesses for the TLA+ evaluator.
//!
//! These harnesses verify critical properties of INSTANCE substitution
//! composition, cache key discrimination, and binding chain scope
//! preservation — the three subsystems that have caused the most
//! regressions (#2995, #2996, #3024, #3030, #3046).
//!
//! Part of #3037 Layer 2: Kani evaluator equivalence harnesses.
//!
//! # Running Verification
//!
//! ```bash
//! cargo kani -p tla-eval --harness compose_with_none_is_identity
//! cargo kani -p tla-eval --harness cache_key_different_instance_subs
//! ```

mod binding_scope_depth5;
mod binding_scope_preservation;
mod cache_key_discrimination;
mod subst_composition;

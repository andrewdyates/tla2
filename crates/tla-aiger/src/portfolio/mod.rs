// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread-based portfolio solver for AIGER safety checking.
//!
//! Runs multiple engines (IC3 variants, BMC, k-induction) in parallel and
//! returns the first definitive result. Uses `Arc<AtomicBool>` for cooperative
//! cancellation.

pub mod adaptive;
pub mod config;
pub mod factory;
pub mod runner;
pub mod safe_witness;

#[cfg(test)]
mod tests;

// Re-export public API for backward compatibility.
pub use adaptive::{
    default_preset_pool, portfolio_check_adaptive, AdaptivePortfolioConfig, AdaptiveScheduler,
};
pub use config::{EngineConfig, PortfolioConfig, PortfolioResult, single_bmc, single_ic3};
pub use factory::*;
pub use runner::{portfolio_check, portfolio_check_detailed};
pub use safe_witness::{validate_safe, validate_safe_with_budget, SafeValidation, SafeWitness};

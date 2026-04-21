// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! InitMode enum and z4 feature flags for initial state enumeration.

/// Mode for initial state enumeration.
///
/// Controls whether to use brute-force enumeration or z4-based SMT solving.
/// This is primarily for testing and allows deterministic selection without
/// relying on environment variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InitMode {
    /// Use brute-force enumeration only (never z4)
    BruteForce,
    /// Use z4 if analysis recommends it, fall back to brute-force if z4 fails
    /// This is the default behavior.
    #[default]
    Auto,
    /// Always try z4 first, fall back to brute-force if z4 fails
    ForceZ4,
}

// Part of #2757: z4-specific feature flags and methods are gated behind
// cfg(feature = "z4"). All production callers (init_solve.rs) are already
// behind this gate; gating the definitions prevents dead code when z4 is
// disabled, rather than relying on test usage to mask the warnings.
#[cfg(feature = "z4")]
feature_flag!(force_z4_enabled, "TLA2_FORCE_Z4");
#[cfg(feature = "z4")]
feature_flag!(auto_z4_enabled, "TLA2_USE_Z4");

#[cfg(feature = "z4")]
impl InitMode {
    /// Resolve effective mode from env vars and config.
    ///
    /// Priority order:
    /// 1. TLA2_FORCE_Z4 env var → ForceZ4 (always try z4)
    /// 2. TLA2_USE_Z4 env var → Auto (use z4 if analysis recommends)
    /// 3. config_mode value (if no env vars set)
    ///
    /// Note: TLA2_USE_Z4 forces Auto mode regardless of config_mode.
    /// This means if config_mode is ForceZ4, setting TLA2_USE_Z4 will
    /// downgrade to Auto. Use TLA2_FORCE_Z4 to override to ForceZ4.
    pub fn resolve(config_mode: InitMode) -> InitMode {
        if force_z4_enabled() {
            InitMode::ForceZ4
        } else if auto_z4_enabled() {
            InitMode::Auto
        } else {
            config_mode
        }
    }

    /// Given analysis needs_z4 result, determine (force_z4, should_try_z4) tuple.
    ///
    /// - `force_z4`: Whether to force z4 even if analysis doesn't recommend it
    /// - `should_try_z4`: Whether to attempt z4-based enumeration
    pub fn z4_decision(self, analysis_needs_z4: bool) -> (bool, bool) {
        match self {
            InitMode::BruteForce => (false, false),
            InitMode::Auto => (false, analysis_needs_z4),
            InitMode::ForceZ4 => (true, true),
        }
    }

    /// Returns true if analysis should be skipped (for optimization).
    ///
    /// When BruteForce mode is set, we can skip expensive analysis.
    pub fn should_skip_analysis(self) -> bool {
        matches!(self, InitMode::BruteForce)
    }
}

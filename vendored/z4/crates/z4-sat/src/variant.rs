// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-COMP solver-variant presets.
//!
//! These presets sit above the low-level `Solver` setters so frontends and
//! packaging scripts can build named SAT variants without duplicating tuning
//! blocks across crates.
//!
//! ## Competition Variants
//!
//! SAT-COMP allows up to 4 solver variants per team. Each variant uses a
//! different configuration profile targeting different problem classes:
//!
//! | Variant | Strategy | Best For |
//! |---------|----------|----------|
//! | `default` | DIMACS SAT packet: stable-only + reduced effort | Baseline CNF |
//! | `aggressive` | Same packet + unconditional full preprocessing | Structured/BMC |
//! | `probe` | Probing + backbone + HBR emphasis | Hard combinatorial |
//! | `minimal` | No inprocessing, fast BCP | Easy/industrial |
//!
//! ## Usage
//!
//! Runtime selection via `Z4_SAT_VARIANT` environment variable or
//! per-variant StarExec run scripts in `competition/bin/`.

use crate::{InprocessingFeatureProfile, Solver};

/// Named SAT-COMP preset selector.
///
/// Four distinct competition variants for SAT-COMP submission. Each targets
/// a different problem class to maximize the portfolio coverage:
///
/// - **Default**: DIMACS SAT packet with stable-only search and reduced BVE/subsumption effort.
/// - **Aggressive**: Same packet, but always runs full preprocessing.
/// - **Probe**: Emphasis on failed-literal probing and backbone detection.
/// - **Minimal**: No inprocessing, fast BCP, conservative search.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum SolverVariant {
    /// Current DIMACS-oriented baseline with all standard features enabled.
    /// Balanced VSIDS + Glucose restarts, quick-mode preprocessing.
    #[default]
    Default,
    /// Higher preprocessing effort and more aggressive simplification.
    /// Full preprocessing, all inprocessing techniques enabled with
    /// tighter scheduling intervals for BVE, subsumption, and vivification.
    Aggressive,
    /// Minimal preprocessing, relying more heavily on CDCL search.
    /// No inprocessing except walk/warmup/shrink for fast BCP throughput.
    Minimal,
    /// Probe-focused: emphasis on failed-literal probing and backbone
    /// detection. Enables probing, backbone, HBR, subsumption, and
    /// transitive reduction while disabling heavyweight techniques
    /// (BVE, vivification, conditioning, sweep, congruence).
    /// Uses Luby restarts (base=250) for more stable search on hard instances.
    Probe,
}

impl SolverVariant {
    /// All currently supported SAT-COMP variants.
    pub const ALL: [Self; 4] = [Self::Default, Self::Aggressive, Self::Minimal, Self::Probe];

    /// Stable external name for the preset.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Default => "default",
            Self::Aggressive => "aggressive",
            Self::Minimal => "minimal",
            Self::Probe => "probe",
        }
    }

    /// Stable executable name used by the build script.
    #[must_use]
    pub const fn binary_name(self) -> &'static str {
        match self {
            Self::Default => "z4-default",
            Self::Aggressive => "z4-aggressive",
            Self::Minimal => "z4-minimal",
            Self::Probe => "z4-probe",
        }
    }

    /// Parse a preset name.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        if name.eq_ignore_ascii_case("default") {
            Some(Self::Default)
        } else if name.eq_ignore_ascii_case("aggressive") {
            Some(Self::Aggressive)
        } else if name.eq_ignore_ascii_case("minimal") {
            Some(Self::Minimal)
        } else if name.eq_ignore_ascii_case("probe") {
            Some(Self::Probe)
        } else {
            None
        }
    }

    /// Resolve a preset into concrete solver settings for the given input.
    #[must_use]
    pub fn config(self, input: VariantInput) -> VariantConfig {
        VariantConfig::for_variant(self, input)
    }
}

/// Input facts used to resolve a preset into concrete solver settings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VariantInput {
    /// Number of variables in the input formula.
    pub num_vars: usize,
    /// Number of clauses in the input formula.
    pub num_clauses: usize,
    /// Whether any proof output is enabled.
    pub proof_mode: bool,
    /// Whether the active proof format is LRAT.
    pub lrat_mode: bool,
}

impl VariantInput {
    /// Construct variant input metadata.
    #[must_use]
    pub const fn new(
        num_vars: usize,
        num_clauses: usize,
        proof_mode: bool,
        lrat_mode: bool,
    ) -> Self {
        Self {
            num_vars,
            num_clauses,
            proof_mode: proof_mode || lrat_mode,
            lrat_mode,
        }
    }
}

/// Restart behavior selected by a variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariantRestartPolicy {
    /// Use the solver's Glucose-style restart controller.
    Glucose,
    /// Use Luby restarts with the provided base interval.
    Luby {
        /// Conflicts per Luby unit.
        base: u64,
    },
}

/// Fully-resolved runtime configuration for a solver variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VariantConfig {
    /// Preset that produced this config.
    pub variant: SolverVariant,
    /// Formula/proof metadata used to resolve the preset.
    pub input: VariantInput,
    /// Whether to request full preprocessing instead of quick mode.
    pub full_preprocessing: bool,
    /// Restart behavior for the preset.
    pub restart_policy: VariantRestartPolicy,
    /// Feature-enable profile applied to the solver.
    pub features: InprocessingFeatureProfile,
}

/// Clause threshold for full preprocessing in Default variant.
/// Raised from 3M to 5M: shuffling-2 (4.7M clauses, 138K vars) benefits from
/// full preprocessing (probing, subsumption, HTR) but was previously stuck in
/// quick mode. CaDiCaL runs full preprocessing regardless of clause count.
/// The expensive-technique gates (CONGRUENCE_MAX_CLAUSES, etc.) separately
/// protect against O(clauses) setup costs.
const DIMACS_FULL_PREPROCESS_MAX_CLAUSES: usize = 5_000_000;
/// BVE effort for large formulas (>5K vars) as per-mille of search propagations.
/// Raised from 10 (1%) to 100 (10%): 1% was too aggressive a reduction --
/// BVE barely ran on large formulas, missing elimination opportunities that
/// reduce the search space. CaDiCaL default is 1000 (100%); 100 (10%) gives
/// meaningful elimination while avoiding pathological BVE overhead on formulas
/// where resolvents blow up (e.g., shuffling-2 produces 450K resolvents).
const DIMACS_REDUCED_EFFORT_BVE: u64 = 100;
/// Subsumption effort for large formulas as per-mille of search propagations.
/// Raised from 60 (6%) to 200 (20%): subsumption is cheap per-step and
/// removes redundant clauses that slow BCP. The per-round overhead is
/// bounded by SUBSUME_MAX_EFFORT.
const DIMACS_REDUCED_EFFORT_SUBSUME: u64 = 200;
const DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS: usize = 5_000;

impl VariantConfig {
    /// Resolve a preset into concrete solver settings.
    #[must_use]
    pub fn for_variant(variant: SolverVariant, input: VariantInput) -> Self {
        let mut config = match variant {
            SolverVariant::Default => Self {
                variant,
                input,
                full_preprocessing: false,
                restart_policy: VariantRestartPolicy::Glucose,
                features: dimacs_baseline_features(),
            },
            SolverVariant::Aggressive => Self {
                variant,
                input,
                full_preprocessing: true,
                restart_policy: VariantRestartPolicy::Glucose,
                features: dimacs_baseline_features(),
            },
            SolverVariant::Minimal => Self {
                variant,
                input,
                full_preprocessing: false,
                restart_policy: VariantRestartPolicy::Glucose,
                features: minimal_features(),
            },
            SolverVariant::Probe => Self {
                variant,
                input,
                full_preprocessing: false,
                restart_policy: VariantRestartPolicy::Luby { base: 250 },
                features: probe_features(),
            },
        };

        if input.lrat_mode {
            config.clamp_for_lrat();
        }

        config
    }

    /// Stable external preset name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        self.variant.as_str()
    }

    /// Stable executable name for this preset.
    #[must_use]
    pub const fn binary_name(self) -> &'static str {
        self.variant.binary_name()
    }

    /// Apply the resolved config to a solver instance.
    ///
    /// Intended for fresh solvers before clauses are added. Frontend debug
    /// overrides should run after this so bisection flags still win.
    pub fn apply_to_solver(&self, solver: &mut Solver) {
        // Keep the historical DIMACS clause threshold: default SAT runs full
        // preprocessing on moderate inputs, but avoids the heavy prepass on
        // multi-million-clause CNF where the SAT packet relies on search.
        let full_preprocessing = match self.variant {
            SolverVariant::Default => self.input.num_clauses <= DIMACS_FULL_PREPROCESS_MAX_CLAUSES,
            _ => self.full_preprocessing,
        };
        solver.set_preprocess_enabled(self.features.preprocess);
        solver.set_full_preprocessing(full_preprocessing);
        solver.set_walk_enabled(self.features.walk);
        solver.set_warmup_enabled(self.features.warmup);
        solver.set_shrink_enabled(self.features.shrink);
        solver.set_hbr_enabled(self.features.hbr);
        solver.set_vivify_enabled(self.features.vivify);
        solver.set_subsume_enabled(self.features.subsume);
        solver.set_probe_enabled(self.features.probe);
        solver.set_bve_enabled(self.features.bve);
        solver.set_bce_enabled(self.features.bce);
        solver.set_condition_enabled(self.features.condition);
        solver.set_decompose_enabled(self.features.decompose);
        solver.set_factor_enabled(self.features.factor);
        solver.set_transred_enabled(self.features.transred);
        solver.set_htr_enabled(self.features.htr);
        solver.set_gate_enabled(self.features.gate);
        solver.set_congruence_enabled(self.features.congruence);
        solver.set_sweep_enabled(self.features.sweep);
        solver.set_backbone_enabled(self.features.backbone);
        solver.set_symmetry_enabled(self.features.symmetry);

        match self.restart_policy {
            VariantRestartPolicy::Glucose => solver.set_glucose_restarts(true),
            VariantRestartPolicy::Luby { base } => {
                solver.set_glucose_restarts(false);
                solver.set_restart_base(base);
            }
        }

        if matches!(
            self.variant,
            SolverVariant::Default | SolverVariant::Aggressive
        ) {
            // CaDiCaL-style focused/stable alternation: the solver starts in
            // focused mode (glucose EMA restarts, VMTF branching) and switches
            // to stable mode (reluctant doubling, VSIDS) after the first phase.
            // This alternation is critical for SAT-COMP performance: focused
            // mode explores broadly via frequent restarts, stable mode exploits
            // via deep search. Previously Z4 locked to stable-only (#7905),
            // which prevented all focused-mode restarts and caused 0 restarts
            // on 60K+ conflicts during the CDCL loop.
            //
            // Reduced BVE/subsumption effort budgets are kept to avoid
            // pathological preprocessing overhead on large formulas.
            if self.input.proof_mode {
                if self.input.num_vars > DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS {
                    solver.set_bve_effort_permille(DIMACS_REDUCED_EFFORT_BVE);
                }
            } else if self.input.num_vars > DIMACS_PROOF_REDUCED_EFFORT_MIN_VARS {
                // Only reduce BVE/subsumption effort on large formulas (>5K vars).
                // Small formulas (like clique 437 vars) need full BVE effort to
                // achieve high elimination rates. CaDiCaL's --sat config reduces
                // effort globally, but CaDiCaL's BVE is more efficient per-step.
                solver.set_bve_effort_permille(DIMACS_REDUCED_EFFORT_BVE);
                solver.set_subsume_effort_permille(DIMACS_REDUCED_EFFORT_SUBSUME);
            }
        }
    }

    fn clamp_for_lrat(&mut self) {
        // #8105: With backward LRAT reconstruction as the primary proof path,
        // all inprocessing techniques are LRAT-compatible. No clamping needed.
        let _ = self;
    }
}

fn dimacs_baseline_features() -> InprocessingFeatureProfile {
    InprocessingFeatureProfile {
        preprocess: true,
        walk: true,
        warmup: true,
        shrink: true,
        hbr: true,
        vivify: true,
        subsume: true,
        probe: true,
        bve: true,
        // CaDiCaL defaults block=0 (DISABLED). BCE removes blocked clauses but
        // adds O(clauses * max_occ) overhead per call. CaDiCaL only enables BCE
        // for specific competition configurations, not the default.
        bce: false,
        // Conditioning (GBCE) eliminates globally blocked clauses and garbage-
        // collects root-satisfied clauses. Per-candidate witness refinement
        // (CaDiCaL condition.cpp:565-705) ensures soundness (#3437).
        condition: true,
        decompose: true,
        factor: true,
        transred: true,
        htr: true,
        gate: true,
        congruence: true,
        sweep: true,
        backbone: true,
        symmetry: true,
    }
}

fn minimal_features() -> InprocessingFeatureProfile {
    InprocessingFeatureProfile {
        preprocess: false,
        walk: true,
        warmup: true,
        shrink: true,
        hbr: false,
        vivify: false,
        subsume: false,
        probe: false,
        bve: false,
        bce: false,
        condition: false,
        decompose: false,
        factor: false,
        transred: false,
        htr: false,
        gate: false,
        congruence: false,
        sweep: false,
        backbone: false,
        symmetry: false,
    }
}

/// Probe-focused feature set for failed-literal probing emphasis.
///
/// Enables: probing, backbone, HBR, subsumption, BCE, HTR, transred,
///          decompose (SCC for equivalences), gate extraction.
/// Disables: BVE, vivification, conditioning, sweep, congruence, factor.
///
/// The rationale is that probing + backbone detection finds fixed literals
/// and binary implications cheaply, while avoiding the heavyweight
/// clause-rewriting techniques that may slow down the search on
/// hard combinatorial instances.
fn probe_features() -> InprocessingFeatureProfile {
    InprocessingFeatureProfile {
        preprocess: true,
        walk: true,
        warmup: true,
        shrink: true,
        hbr: true,
        vivify: false,
        subsume: true,
        probe: true,
        bve: false,
        bce: true,
        condition: false,
        decompose: true,
        factor: false,
        transred: true,
        htr: true,
        gate: true,
        congruence: false,
        sweep: false,
        backbone: true,
        symmetry: true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_variant_matches_dimacs_baseline() {
        let config = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(32, 96, false, false),
        );

        assert!(!config.full_preprocessing);
        assert!(config.features.preprocess);
        assert!(config.features.bve);
        assert!(config.features.congruence);
        assert!(config.features.subsume);
    }

    #[test]
    fn test_aggressive_variant_enables_full_preprocessing() {
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, false, false),
        );

        assert!(config.full_preprocessing);
        assert_eq!(config.restart_policy, VariantRestartPolicy::Glucose);
    }

    #[test]
    fn test_minimal_variant_disables_preprocessing_pipeline() {
        let config = VariantConfig::for_variant(
            SolverVariant::Minimal,
            VariantInput::new(32, 96, false, false),
        );

        assert!(!config.features.preprocess);
        assert!(config.features.walk);
        assert!(config.features.warmup);
        assert!(config.features.shrink);
        assert!(!config.features.bve);
        assert!(!config.features.vivify);
        assert!(!config.features.probe);
    }

    #[test]
    fn test_probe_variant_enables_probing_backbone() {
        let config = VariantConfig::for_variant(
            SolverVariant::Probe,
            VariantInput::new(32, 96, false, false),
        );

        // Core probe-focused features enabled
        assert!(config.features.probe);
        assert!(config.features.backbone);
        assert!(config.features.hbr);
        assert!(config.features.subsume);
        assert!(config.features.transred);
        assert!(config.features.htr);
        assert!(config.features.gate);
        assert!(config.features.decompose);
        assert!(config.features.bce);

        // Heavyweight techniques disabled
        assert!(!config.features.bve);
        assert!(!config.features.vivify);
        assert!(!config.features.condition);
        assert!(!config.features.sweep);
        assert!(!config.features.congruence);
        assert!(!config.features.factor);

        // Uses Luby restarts
        assert_eq!(
            config.restart_policy,
            VariantRestartPolicy::Luby { base: 250 }
        );
        assert!(!config.full_preprocessing);
    }

    #[test]
    fn test_lrat_input_keeps_all_features_enabled() {
        // #8105: backward LRAT reconstruction enables all features in LRAT mode
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, true, true),
        );

        assert!(config.features.probe, "probe: LRAT-safe with backward reconstruction (#8105)");
        assert!(config.features.factor, "factor: LRAT-safe with backward reconstruction (#8105)");
        assert!(config.features.sweep, "sweep: LRAT-safe with backward reconstruction (#8105)");
    }

    #[test]
    fn test_apply_to_solver_sets_feature_profile() {
        let config = VariantConfig::for_variant(
            SolverVariant::Aggressive,
            VariantInput::new(32, 96, false, false),
        );
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        assert!(solver.is_preprocess_enabled());
        assert!(solver.is_full_preprocessing_enabled());
        assert_eq!(solver.inprocessing_feature_profile(), config.features);
        // CaDiCaL-style focused/stable alternation (not stable-only).
        assert!(!solver.stable_only_enabled());
        // Small formulas (<5K vars) get full BVE/subsumption effort.
        assert_eq!(solver.bve_effort_permille(), 1000);
    }

    #[test]
    fn test_default_variant_restores_dimacs_sat_packet() {
        let config = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(32, 96, false, false),
        );
        let mut solver = Solver::new(32);
        config.apply_to_solver(&mut solver);

        // CaDiCaL-style focused/stable alternation (not stable-only).
        assert!(!solver.stable_only_enabled());
        assert!(solver.is_full_preprocessing_enabled());
        // Small formulas (<5K vars) get full BVE/subsumption effort.
        assert_eq!(solver.bve_effort_permille(), 1000);
    }

    #[test]
    fn test_default_variant_large_formula_stays_in_quick_preprocess() {
        let config = VariantConfig::for_variant(
            SolverVariant::Default,
            VariantInput::new(10_000, DIMACS_FULL_PREPROCESS_MAX_CLAUSES + 1, false, false),
        );
        let mut solver = Solver::new(10_000);
        config.apply_to_solver(&mut solver);

        // CaDiCaL-style focused/stable alternation (not stable-only).
        assert!(!solver.stable_only_enabled());
        assert!(!solver.is_full_preprocessing_enabled());
    }

    #[test]
    fn test_all_variants_have_unique_names() {
        let names: Vec<&str> = SolverVariant::ALL.iter().map(|v| v.as_str()).collect();
        let mut unique = names.clone();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(names.len(), unique.len(), "variant names must be unique");
    }

    #[test]
    fn test_all_variants_have_unique_binary_names() {
        let names: Vec<&str> = SolverVariant::ALL.iter().map(|v| v.binary_name()).collect();
        let mut unique = names.clone();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(names.len(), unique.len(), "binary names must be unique");
    }

    #[test]
    fn test_parse_roundtrip() {
        for variant in SolverVariant::ALL {
            let name = variant.as_str();
            let parsed = SolverVariant::parse(name);
            assert_eq!(parsed, Some(variant), "parse('{name}') should roundtrip");
        }
    }

    #[test]
    fn test_parse_unknown_returns_none() {
        assert_eq!(SolverVariant::parse("nonexistent"), None);
        assert_eq!(SolverVariant::parse(""), None);
    }

    #[test]
    fn test_four_variants_produce_distinct_configs() {
        let input = VariantInput::new(1000, 5000, false, false);
        let configs: Vec<VariantConfig> =
            SolverVariant::ALL.iter().map(|v| v.config(input)).collect();

        // Verify that no two configs are identical
        for i in 0..configs.len() {
            for j in (i + 1)..configs.len() {
                let same_features = configs[i].features == configs[j].features;
                let same_restart = configs[i].restart_policy == configs[j].restart_policy;
                let same_preproc = configs[i].full_preprocessing == configs[j].full_preprocessing;
                assert!(
                    !(same_features && same_restart && same_preproc),
                    "variants {} and {} must differ in at least one dimension",
                    configs[i].name(),
                    configs[j].name(),
                );
            }
        }
    }
}

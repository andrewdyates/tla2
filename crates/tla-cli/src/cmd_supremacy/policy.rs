// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed policy model for `tla2 supremacy`.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

use crate::cli_schema::{SupremacyGateMode, SupremacyMode};

#[derive(Clone, Debug, Deserialize, Serialize)]
pub(super) struct SupremacyPolicy {
    pub(super) specs: Vec<String>,
    #[serde(default)]
    pub(super) expected_state_counts: BTreeMap<String, u64>,
    #[serde(default)]
    pub(super) expected_generated_state_counts: BTreeMap<String, u64>,
    #[serde(default)]
    pub(super) required_llvm2_gate_flags: Vec<String>,
    #[serde(default)]
    pub(super) default_gate_mode: Option<String>,
    #[serde(default)]
    pub(super) final_gate_mode: Option<String>,
    #[serde(default)]
    pub(super) gate_modes: BTreeMap<String, GateModePolicy>,
    #[serde(default)]
    pub(super) thresholds: BTreeMap<String, ThresholdPolicy>,
}

impl SupremacyPolicy {
    pub(super) fn load(path: &Path) -> Result<Self> {
        let text = fs::read_to_string(path)
            .with_context(|| format!("read supremacy policy {}", path.display()))?;
        let policy: Self = serde_json::from_str(&text)
            .with_context(|| format!("parse supremacy policy {}", path.display()))?;
        policy.validate_specs()?;
        Ok(policy)
    }

    pub(super) fn resolve_gate_mode(
        &self,
        run_mode: SupremacyMode,
        requested: Option<SupremacyGateMode>,
    ) -> Result<ResolvedGateMode<'_>> {
        if self.gate_modes.is_empty() {
            let name = requested
                .map(policy_gate_mode_key)
                .or(self.default_gate_mode.as_deref())
                .unwrap_or("legacy");
            return Ok(ResolvedGateMode {
                name,
                policy: None,
                benchmark_flags: self.required_llvm2_gate_flags.clone(),
            });
        }

        let name = match run_mode {
            SupremacyMode::Enforce => self
                .final_gate_mode
                .as_deref()
                .or(self.default_gate_mode.as_deref())
                .context("policy has gate_modes but no final_gate_mode/default_gate_mode")?,
            SupremacyMode::Warn => requested
                .map(policy_gate_mode_key)
                .or(self.default_gate_mode.as_deref())
                .context("policy has gate_modes but no requested/default gate mode")?,
        };
        let policy = self.gate_modes.get(name).with_context(|| {
            let available = self
                .gate_modes
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>()
                .join(", ");
            format!("unknown gate mode {name:?}; available: {available}")
        })?;
        Ok(ResolvedGateMode {
            name,
            policy: Some(policy),
            benchmark_flags: policy.benchmark_flags.clone(),
        })
    }

    pub(super) fn validate_gate_ready(&self) -> Result<()> {
        self.validate_specs()?;
        if self.specs.is_empty() {
            bail!("supremacy policy must list at least one spec");
        }
        for spec in &self.specs {
            let Some(expected_states) = self.expected_state_counts.get(spec) else {
                bail!("supremacy gate policy missing expected_state_counts[{spec:?}]");
            };
            if *expected_states == 0 {
                bail!("supremacy gate policy expected_state_counts[{spec:?}] must be positive");
            }
            let Some(expected_generated) = self.expected_generated_state_counts.get(spec) else {
                bail!("supremacy gate policy missing expected_generated_state_counts[{spec:?}]");
            };
            if *expected_generated == 0 {
                bail!(
                    "supremacy gate policy expected_generated_state_counts[{spec:?}] must be positive"
                );
            }
            let Some(thresholds) = self.thresholds.get(spec) else {
                bail!("supremacy gate policy missing thresholds[{spec:?}]");
            };
            thresholds.validate(spec)?;
        }
        require_non_empty_strings(&self.required_llvm2_gate_flags, "required_llvm2_gate_flags")?;
        if self.gate_modes.is_empty() {
            bail!("supremacy gate policy must define at least one gate mode");
        }
        for (name, mode) in &self.gate_modes {
            mode.validate(name)?;
        }
        for field in [&self.default_gate_mode, &self.final_gate_mode]
            .into_iter()
            .flatten()
        {
            if !self.gate_modes.contains_key(field) {
                bail!("supremacy gate policy references unknown gate mode {field:?}");
            }
        }
        Ok(())
    }

    fn validate_specs(&self) -> Result<()> {
        if self.specs.is_empty() {
            bail!("supremacy policy must list at least one spec");
        }
        for spec in &self.specs {
            if spec.is_empty() {
                bail!("supremacy policy specs must not contain empty names");
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub(super) struct GateModePolicy {
    #[serde(default)]
    pub(super) description: Option<String>,
    #[serde(default)]
    pub(super) benchmark_flags: Vec<String>,
    #[serde(default)]
    pub(super) forbidden_benchmark_flags: Vec<String>,
    #[serde(default)]
    pub(super) required_llvm2_env: BTreeMap<String, String>,
    #[serde(default)]
    pub(super) required_llvm2_compilation_total_matches: Vec<String>,
    #[serde(default)]
    pub(super) require_generated_state_parity_by_run_index: bool,
    #[serde(default)]
    pub(super) required_llvm2_run_telemetry: BTreeMap<String, TelemetryRequirement>,
    #[serde(default)]
    pub(super) required_llvm2_run_telemetry_by_spec:
        BTreeMap<String, BTreeMap<String, TelemetryRequirement>>,
    #[serde(default)]
    pub(super) required_llvm2_selftest_by_spec: BTreeMap<String, SelftestRequirement>,
}

impl GateModePolicy {
    fn validate(&self, name: &str) -> Result<()> {
        if name.is_empty() {
            bail!("supremacy gate policy gate_modes must not contain an empty mode name");
        }
        if self.benchmark_flags.is_empty() {
            bail!("supremacy gate policy gate_modes.{name}.benchmark_flags must not be empty");
        }
        require_non_empty_strings(
            &self.benchmark_flags,
            &format!("gate_modes.{name}.benchmark_flags"),
        )?;
        require_non_empty_strings(
            &self.forbidden_benchmark_flags,
            &format!("gate_modes.{name}.forbidden_benchmark_flags"),
        )?;
        require_non_empty_strings(
            &self.required_llvm2_compilation_total_matches,
            &format!("gate_modes.{name}.required_llvm2_compilation_total_matches"),
        )?;
        require_non_empty_string_map(
            &self.required_llvm2_env,
            &format!("gate_modes.{name}.required_llvm2_env"),
        )?;
        for (field, requirement) in &self.required_llvm2_run_telemetry {
            requirement.validate(&format!(
                "gate_modes.{name}.required_llvm2_run_telemetry.{field}"
            ))?;
        }
        for (spec, requirements) in &self.required_llvm2_run_telemetry_by_spec {
            if spec.is_empty() {
                bail!(
                    "supremacy gate policy gate_modes.{name}.required_llvm2_run_telemetry_by_spec contains empty spec"
                );
            }
            for (field, requirement) in requirements {
                requirement.validate(&format!(
                    "gate_modes.{name}.required_llvm2_run_telemetry_by_spec.{spec}.{field}"
                ))?;
            }
        }
        for (spec, requirement) in &self.required_llvm2_selftest_by_spec {
            requirement.validate(&format!(
                "gate_modes.{name}.required_llvm2_selftest_by_spec.{spec}"
            ))?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq)]
#[serde(untagged)]
pub(super) enum TelemetryRequirement {
    Bool(bool),
    Integer(i64),
    Text(String),
}

impl TelemetryRequirement {
    fn validate(&self, path: &str) -> Result<()> {
        if let Self::Text(value) = self {
            if value.is_empty() {
                bail!("supremacy gate policy {path} must not be an empty string");
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub(super) struct SelftestRequirement {
    pub(super) actions: u64,
    pub(super) state_constraints: u64,
    pub(super) invariants: u64,
    pub(super) state_len: u64,
}

impl SelftestRequirement {
    fn validate(&self, path: &str) -> Result<()> {
        if self.actions == 0 {
            bail!("supremacy gate policy {path}.actions must be positive");
        }
        if self.state_len == 0 {
            bail!("supremacy gate policy {path}.state_len must be positive");
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub(super) struct ThresholdPolicy {
    #[serde(default)]
    pub(super) min_speedup_interp_vs_tlc: Option<f64>,
    #[serde(default)]
    pub(super) min_speedup_llvm2_vs_tlc: Option<f64>,
    #[serde(default)]
    pub(super) min_llvm2_vs_interp_ratio: Option<f64>,
}

impl ThresholdPolicy {
    fn validate(&self, spec: &str) -> Result<()> {
        validate_positive_threshold(
            self.min_speedup_interp_vs_tlc,
            spec,
            "min_speedup_interp_vs_tlc",
        )?;
        validate_positive_threshold(
            self.min_speedup_llvm2_vs_tlc,
            spec,
            "min_speedup_llvm2_vs_tlc",
        )?;
        validate_positive_threshold(
            self.min_llvm2_vs_interp_ratio,
            spec,
            "min_llvm2_vs_interp_ratio",
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct PlannedGate {
    pub(super) gate_mode: String,
    pub(super) benchmark_flags: Vec<String>,
    pub(super) forbidden_benchmark_flags: Vec<String>,
    pub(super) required_llvm2_env: BTreeMap<String, String>,
    pub(super) required_llvm2_compilation_total_matches: Vec<String>,
    pub(super) require_generated_state_parity_by_run_index: bool,
    pub(super) required_llvm2_run_telemetry: BTreeMap<String, TelemetryRequirement>,
    pub(super) required_llvm2_run_telemetry_by_spec:
        BTreeMap<String, BTreeMap<String, TelemetryRequirement>>,
    pub(super) required_llvm2_selftest_by_spec: BTreeMap<String, SelftestRequirement>,
}

impl PlannedGate {
    pub(super) fn from_resolved(resolved: ResolvedGateMode<'_>) -> Self {
        let Some(policy) = resolved.policy else {
            return Self {
                gate_mode: resolved.name.to_string(),
                benchmark_flags: resolved.benchmark_flags,
                forbidden_benchmark_flags: Vec::new(),
                required_llvm2_env: BTreeMap::new(),
                required_llvm2_compilation_total_matches: Vec::new(),
                require_generated_state_parity_by_run_index: false,
                required_llvm2_run_telemetry: BTreeMap::new(),
                required_llvm2_run_telemetry_by_spec: BTreeMap::new(),
                required_llvm2_selftest_by_spec: BTreeMap::new(),
            };
        };
        Self {
            gate_mode: resolved.name.to_string(),
            benchmark_flags: resolved.benchmark_flags,
            forbidden_benchmark_flags: policy.forbidden_benchmark_flags.clone(),
            required_llvm2_env: policy.required_llvm2_env.clone(),
            required_llvm2_compilation_total_matches: policy
                .required_llvm2_compilation_total_matches
                .clone(),
            require_generated_state_parity_by_run_index: policy
                .require_generated_state_parity_by_run_index,
            required_llvm2_run_telemetry: policy.required_llvm2_run_telemetry.clone(),
            required_llvm2_run_telemetry_by_spec: policy
                .required_llvm2_run_telemetry_by_spec
                .clone(),
            required_llvm2_selftest_by_spec: policy.required_llvm2_selftest_by_spec.clone(),
        }
    }

    pub(super) fn enforce_required_env(&self) -> BTreeMap<String, String> {
        let mut required = BTreeMap::new();
        if self.gate_mode == "full_native_fused" {
            required.extend(full_native_fused_protected_env());
        }
        required.extend(self.required_llvm2_env.clone());
        required
    }
}

pub(super) struct ResolvedGateMode<'a> {
    pub(super) name: &'a str,
    pub(super) policy: Option<&'a GateModePolicy>,
    pub(super) benchmark_flags: Vec<String>,
}

pub(super) fn policy_gate_mode_key(mode: SupremacyGateMode) -> &'static str {
    match mode {
        SupremacyGateMode::InterimActionOnlyNativeFused => "interim_action_only_native_fused",
        SupremacyGateMode::FullNativeFused => "full_native_fused",
    }
}

pub(super) fn cli_gate_mode_name(mode: SupremacyGateMode) -> &'static str {
    match mode {
        SupremacyGateMode::InterimActionOnlyNativeFused => "interim-action-only-native-fused",
        SupremacyGateMode::FullNativeFused => "full-native-fused",
    }
}

fn full_native_fused_protected_env() -> BTreeMap<String, String> {
    [
        ("TLA2_LLVM2", "1"),
        ("TLA2_LLVM2_BFS", "1"),
        ("TLA2_LLVM2_EXISTS", "1"),
        ("TLA2_COMPILED_BFS", "1"),
        ("TLA2_FLAT_BFS", "1"),
        ("TLA2_BYTECODE_VM", "1"),
        ("TLA2_BYTECODE_VM_STATS", "1"),
        ("TLA2_AUTO_POR", "0"),
        ("TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST", "strict"),
        ("TLA2_LLVM2_NATIVE_FUSED_STRICT", "1"),
        ("TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL", "O3"),
        ("TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL", "O3"),
        ("TLA2_LLVM2_DISABLE_POST_RA_OPT", "0"),
        ("TLA2_DISABLE_ARTIFACT_CACHE", "1"),
        ("TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP", "1"),
    ]
    .into_iter()
    .map(|(key, value)| (key.to_string(), value.to_string()))
    .collect()
}

fn require_non_empty_strings(values: &[String], path: &str) -> Result<()> {
    if let Some(value) = values.iter().find(|value| value.is_empty()) {
        bail!("supremacy policy {path} contains empty string {value:?}");
    }
    Ok(())
}

fn require_non_empty_string_map(values: &BTreeMap<String, String>, path: &str) -> Result<()> {
    for (key, value) in values {
        if key.is_empty() {
            bail!("supremacy policy {path} contains empty key");
        }
        if value.is_empty() {
            bail!("supremacy policy {path}.{key} contains empty value");
        }
    }
    Ok(())
}

fn validate_positive_threshold(value: Option<f64>, spec: &str, field: &str) -> Result<()> {
    let Some(value) = value else {
        return Ok(());
    };
    if !value.is_finite() || value <= 0.0 {
        bail!("supremacy gate policy thresholds[{spec:?}].{field} must be positive");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn repo_policy_path() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("tests/tlc_comparison/single_thread_supremacy_gate.json")
    }

    #[test]
    fn parses_policy_gate_modes() {
        let policy = SupremacyPolicy::load(&repo_policy_path()).unwrap();
        policy.validate_gate_ready().unwrap();

        let full = policy
            .resolve_gate_mode(
                SupremacyMode::Enforce,
                Some(SupremacyGateMode::InterimActionOnlyNativeFused),
            )
            .unwrap();
        assert_eq!(full.name, "full_native_fused");
        assert!(full
            .benchmark_flags
            .contains(&"require_llvm2_compiled_invariants".to_string()));

        let planned = PlannedGate::from_resolved(full);
        assert_eq!(
            planned
                .required_llvm2_env
                .get("TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST")
                .map(String::as_str),
            Some("strict")
        );
        assert!(planned.require_generated_state_parity_by_run_index);
        assert!(planned
            .required_llvm2_run_telemetry
            .contains_key("compiled_bfs_execution_nanos"));
        assert!(planned
            .required_llvm2_selftest_by_spec
            .contains_key("MCLamportMutex"));
    }

    #[test]
    fn loads_minimal_policy_for_smoke_specs() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("policy.json");
        fs::write(&path, r#"{"specs":["TinySpec"]}"#).unwrap();

        let policy = SupremacyPolicy::load(&path).unwrap();

        assert_eq!(policy.specs, vec!["TinySpec".to_string()]);
        assert!(policy.validate_gate_ready().is_err());
    }

    #[test]
    fn maps_cli_gate_modes_to_policy_keys() {
        assert_eq!(
            policy_gate_mode_key(SupremacyGateMode::FullNativeFused),
            "full_native_fused"
        );
        assert_eq!(
            cli_gate_mode_name(SupremacyGateMode::FullNativeFused),
            "full-native-fused"
        );
    }

    #[test]
    fn enforce_required_env_includes_wrapper_protected_controls() {
        let planned = PlannedGate {
            gate_mode: "full_native_fused".to_string(),
            benchmark_flags: Vec::new(),
            forbidden_benchmark_flags: Vec::new(),
            required_llvm2_env: BTreeMap::new(),
            required_llvm2_compilation_total_matches: Vec::new(),
            require_generated_state_parity_by_run_index: false,
            required_llvm2_run_telemetry: BTreeMap::new(),
            required_llvm2_run_telemetry_by_spec: BTreeMap::new(),
            required_llvm2_selftest_by_spec: BTreeMap::new(),
        };

        let required = planned.enforce_required_env();
        assert_eq!(required.get("TLA2_LLVM2").map(String::as_str), Some("1"));
        assert_eq!(
            required
                .get("TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL")
                .map(String::as_str),
            Some("O3")
        );
    }
}

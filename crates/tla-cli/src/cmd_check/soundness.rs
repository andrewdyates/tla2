// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(crate) fn soundness_mode_rank(mode: SoundnessMode) -> u8 {
    match mode {
        SoundnessMode::Sound => 0,
        SoundnessMode::Experimental => 1,
        SoundnessMode::Heuristic => 2,
        _ => u8::MAX,
    }
}

pub(crate) fn allowed_soundness_mode(gate: SoundnessGate) -> SoundnessMode {
    match gate {
        SoundnessGate::Sound => SoundnessMode::Sound,
        SoundnessGate::Experimental => SoundnessMode::Experimental,
        SoundnessGate::Heuristic => SoundnessMode::Heuristic,
    }
}

#[allow(clippy::fn_params_excessive_bools)]
pub(crate) fn compute_cli_soundness_provenance(
    pdr_enabled: bool,
    _por_enabled: bool,
    bmc_depth: usize,
    completeness: SearchCompleteness,
    has_properties: bool,
    skip_liveness_for_benchmark: bool,
) -> SoundnessProvenance {
    let mut provenance = SoundnessProvenance::sound();

    if pdr_enabled {
        if soundness_mode_rank(SoundnessMode::Experimental) > soundness_mode_rank(provenance.mode) {
            provenance.mode = SoundnessMode::Experimental;
        }
        provenance.features_used.push("pdr".to_string());
        provenance
            .deviations
            .push("PDR is experimental and only supports a subset of TLA+".to_string());
    }

    if bmc_depth > 0 {
        if soundness_mode_rank(SoundnessMode::Heuristic) > soundness_mode_rank(provenance.mode) {
            provenance.mode = SoundnessMode::Heuristic;
        }
        provenance.features_used.push("bmc".to_string());
        provenance.deviations.push(format!(
            "BMC is heuristic/incomplete (configured depth={})",
            bmc_depth
        ));
    }

    if has_properties && skip_liveness_for_benchmark {
        provenance.features_used.push("skip_liveness".to_string());
        provenance.deviations.push(
            "PROPERTY/liveness checking is disabled by TLA2_SKIP_LIVENESS=1 (benchmark mode)"
                .to_string(),
        );
    }

    match completeness {
        SearchCompleteness::Exhaustive => {}
        SearchCompleteness::BoundedDepth { .. } => {
            provenance.features_used.push("bounded_depth".to_string());
        }
        SearchCompleteness::BoundedStates { .. } => {
            provenance.features_used.push("bounded_states".to_string());
        }
        SearchCompleteness::Bounded { .. } => {
            provenance.features_used.push("bounded_states".to_string());
            provenance.features_used.push("bounded_depth".to_string());
        }
        _ => {}
    }

    provenance
}

pub(crate) fn print_provenance_human(
    soundness: &SoundnessProvenance,
    completeness: SearchCompleteness,
) {
    println!("Provenance:");
    println!("  Soundness mode: {:?}", soundness.mode);
    println!("  Search completeness: {}", completeness.format_human());
    if !soundness.features_used.is_empty() {
        println!("  Features used ({}):", soundness.features_used.len());
        for feature in &soundness.features_used {
            println!("    {}", feature);
        }
    }
    if !soundness.deviations.is_empty() {
        println!("  Deviations ({}):", soundness.deviations.len());
        for deviation in &soundness.deviations {
            println!("    {}", deviation);
        }
    }
    if !soundness.assumptions.is_empty() {
        println!("  Assumptions ({}):", soundness.assumptions.len());
        for assumption in &soundness.assumptions {
            println!("    {}", assumption);
        }
    }
}

/// Shared context for soundness/completeness gate output.
pub(super) struct GateOutputCtx<'a> {
    pub(super) file: &'a Path,
    pub(super) config_path: &'a Path,
    pub(super) module_name: &'a str,
    pub(super) workers: usize,
    pub(super) output_format: OutputFormat,
}

/// Enforce soundness gating: bail if the run's soundness mode exceeds the gate.
pub(super) fn enforce_soundness_gate(
    soundness_gate: SoundnessGate,
    soundness: &SoundnessProvenance,
    completeness: SearchCompleteness,
    gate_ctx: &GateOutputCtx<'_>,
) -> Result<()> {
    let allowed_mode = allowed_soundness_mode(soundness_gate);
    if soundness_mode_rank(soundness.mode) <= soundness_mode_rank(allowed_mode) {
        return Ok(());
    }
    let msg = format!(
        "Soundness gate failed: run mode is {:?}. Re-run with --soundness {} to proceed.",
        soundness.mode,
        match soundness.mode {
            SoundnessMode::Sound => "sound",
            SoundnessMode::Experimental => "experimental",
            SoundnessMode::Heuristic => "heuristic",
            _ => "unknown",
        }
    );
    if matches!(gate_ctx.output_format, OutputFormat::Itf) {
        eprintln!("Error: {}", msg);
        std::process::exit(2);
    }
    if matches!(
        gate_ctx.output_format,
        OutputFormat::Json | OutputFormat::Jsonl
    ) {
        let json_output = JsonOutput::new(
            gate_ctx.file,
            Some(gate_ctx.config_path),
            gate_ctx.module_name,
            gate_ctx.workers,
        )
        .with_soundness(soundness.clone())
        .with_completeness(completeness)
        .with_cli_error(
            error_codes::SYS_SOUNDNESS_GATED,
            msg,
            Some(
                ErrorSuggestion::new("Re-run with a less strict soundness gate")
                    .with_example("tla2 check ... --soundness experimental")
                    .with_options(vec![
                        "--soundness experimental".to_string(),
                        "--soundness heuristic".to_string(),
                    ]),
            ),
        );
        let json_str = if matches!(gate_ctx.output_format, OutputFormat::Jsonl) {
            json_output.to_json_compact().context("serialize JSON")?
        } else {
            json_output.to_json().context("serialize JSON")?
        };
        println!("{}", json_str);
        std::process::exit(2);
    }
    if matches!(gate_ctx.output_format, OutputFormat::Human) {
        print_provenance_human(soundness, completeness);
        println!();
    }
    bail!("{}", msg);
}

/// Enforce completeness gating: bail if --require-exhaustive and bounds are set.
pub(super) fn enforce_completeness_gate(
    require_exhaustive: bool,
    soundness: &SoundnessProvenance,
    completeness: SearchCompleteness,
    gate_ctx: &GateOutputCtx<'_>,
) -> Result<()> {
    if !require_exhaustive || completeness.is_exhaustive() {
        return Ok(());
    }
    let msg = format!(
        "Completeness gate failed: run is {}. Re-run without bounds to proceed.",
        completeness.format_human()
    );
    if matches!(gate_ctx.output_format, OutputFormat::Itf) {
        eprintln!("Error: {}", msg);
        std::process::exit(2);
    }
    if matches!(
        gate_ctx.output_format,
        OutputFormat::Json | OutputFormat::Jsonl
    ) {
        let json_output = JsonOutput::new(
            gate_ctx.file,
            Some(gate_ctx.config_path),
            gate_ctx.module_name,
            gate_ctx.workers,
        )
        .with_soundness(soundness.clone())
        .with_completeness(completeness)
        .with_cli_error(
            error_codes::SYS_COMPLETENESS_GATED,
            msg,
            Some(
                ErrorSuggestion::new("Re-run without bounds for exhaustive exploration")
                    .with_example("tla2 check ... --max-states 0 --max-depth 0")
                    .with_options(vec![
                        "--max-states 0".to_string(),
                        "--max-depth 0".to_string(),
                    ]),
            ),
        );
        let json_str = if matches!(gate_ctx.output_format, OutputFormat::Jsonl) {
            json_output.to_json_compact().context("serialize JSON")?
        } else {
            json_output.to_json().context("serialize JSON")?
        };
        println!("{}", json_str);
        std::process::exit(2);
    }
    if matches!(gate_ctx.output_format, OutputFormat::Human) {
        print_provenance_human(soundness, completeness);
        println!();
    }
    bail!("{}", msg);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_trace_with_properties_adds_liveness_skip_deviation() {
        let provenance = compute_cli_soundness_provenance(
            false,
            false,
            0,
            SearchCompleteness::Exhaustive,
            true,
            false,
        );

        assert!(
            !provenance.features_used.iter().any(|f| f == "no_trace"),
            "did not expect no_trace feature marker; --no-trace no longer disables liveness, got {:?}",
            provenance.features_used
        );
        assert!(
            !provenance
                .deviations
                .iter()
                .any(|d| d.contains("--no-trace") && d.contains("PROPERTY/liveness")),
            "did not expect no-trace/property deviation; --no-trace no longer disables liveness, got {:?}",
            provenance.deviations
        );
    }

    #[test]
    fn skip_liveness_env_with_properties_adds_benchmark_deviation() {
        let provenance = compute_cli_soundness_provenance(
            false,
            false,
            0,
            SearchCompleteness::Exhaustive,
            true,
            true,
        );

        assert!(
            provenance
                .features_used
                .iter()
                .any(|f| f == "skip_liveness"),
            "expected skip_liveness feature marker, got {:?}",
            provenance.features_used
        );
        assert!(
            provenance
                .deviations
                .iter()
                .any(|d| d.contains("TLA2_SKIP_LIVENESS=1")),
            "expected skip-liveness deviation, got {:?}",
            provenance.deviations
        );
    }

    #[test]
    fn properties_without_skip_liveness_deviation_stay_sound() {
        let provenance = compute_cli_soundness_provenance(
            false,
            false,
            0,
            SearchCompleteness::Exhaustive,
            true,
            false,
        );

        assert!(
            !provenance.features_used.iter().any(|f| f == "no_trace"),
            "did not expect no_trace feature marker when liveness remains enabled, got {:?}",
            provenance.features_used
        );
        assert!(
            !provenance
                .deviations
                .iter()
                .any(|d| d.contains("--no-trace") && d.contains("PROPERTY/liveness")),
            "did not expect no-trace/property deviation when liveness remains enabled, got {:?}",
            provenance.deviations
        );
    }
}

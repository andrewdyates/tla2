// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA2 trace integration for PDR solver transitions.
//!
//! Emits compact runtime snapshots for validating PDR action sequences against
//! `specs/pdr_test.tla`.

use super::PdrSolver;
use crate::pdr::frame::PdrResult;
use crate::pdr::obligation::ProofObligation;
use z4_sat::{TlaTraceWriter, TlaTraceable};

const PDR_TRACE_MODULE: &str = "pdr_test";
const PDR_TRACE_VARIABLES: [&str; 8] = [
    "frames",
    "obligations",
    "currentLevel",
    "result",
    "lemmaCount",
    "activePredicate",
    "activeLevel",
    "obligationDepth",
];

impl TlaTraceable for PdrSolver {
    fn tla_module() -> &'static str {
        PDR_TRACE_MODULE
    }

    fn tla_variables() -> &'static [&'static str] {
        &PDR_TRACE_VARIABLES
    }

    /// Enable TLA2 JSONL trace emission for this solver instance.
    ///
    /// Writes an initial step (index 0) immediately with action = None.
    fn enable_tla_trace(&mut self, path: &str, module: &str, variables: &[&str]) {
        self.tracing.tla_trace = Some(TlaTraceWriter::new(path, module, variables));
        self.pdr_trace_step("Running", None, None);
    }
}

impl PdrSolver {
    /// Enable trace output on an explicit path.
    pub(in crate::pdr::solver) fn enable_tla_trace_from_path(&mut self, path: &str) {
        <Self as TlaTraceable>::enable_tla_trace(
            self,
            path,
            PDR_TRACE_MODULE,
            &PDR_TRACE_VARIABLES,
        );
    }

    /// Enable trace output from the path captured in the solver config.
    ///
    /// This is intended for top-level PDR solve entry points that already
    /// captured `Z4_TRACE_FILE` in `PdrConfig` and must not re-read the
    /// environment. If tracing is already enabled, leave the active writer
    /// untouched to avoid clobbering the JSONL file.
    pub(crate) fn enable_tla_trace_from_config(&mut self) {
        if self.tracing.tla_trace.is_some() {
            return;
        }
        if let Some(path) = self.config.tla_trace_path.clone() {
            self.enable_tla_trace_from_path(&path);
        }
    }

    fn obligations_len(&self) -> usize {
        if self.config.use_level_priority {
            self.obligations.heap.len()
        } else {
            self.obligations.deque.len()
        }
    }

    fn usize_to_i64(value: usize) -> i64 {
        i64::try_from(value).unwrap_or(i64::MAX)
    }

    /// Build a TLA2 state snapshot aligned with `specs/pdr_test.tla`.
    ///
    /// `active_pob` provides obligation context when processing an obligation.
    /// Pass `None` for non-obligation actions (Init, ExpandLevel, PropagateLemmas, terminal).
    fn pdr_trace_snapshot(
        &self,
        result: &str,
        active_pob: Option<&ProofObligation>,
    ) -> serde_json::Value {
        let frame_count = Self::usize_to_i64(self.frames.len());
        let obligations = Self::usize_to_i64(self.obligations_len());
        // Use the independently-tracked query level instead of computing from frames.len().
        // This makes `FrameMonotonicity` (currentLevel = frames - 1) non-vacuous:
        // the invariant can now detect bugs where the query level falls out of sync
        // with the frame count (e.g., missing push_frame update, stale level after restart).
        let current_level = match self.tracing.query_level {
            Some(level) => Self::usize_to_i64(level),
            None => Self::usize_to_i64(self.frames.len().saturating_sub(1)),
        };
        let lemma_count: usize = self.frames.iter().map(|f| f.lemmas.len()).sum();

        let (active_pred, active_lvl, ob_depth) = match active_pob {
            Some(pob) => (
                pob.predicate.index() as i64,
                pob.level as i64,
                pob.depth as i64,
            ),
            None => match self.tracing.active_pob {
                Some((pred_idx, level, depth)) => (pred_idx as i64, level as i64, depth as i64),
                None => (-1_i64, -1_i64, 0_i64),
            },
        };

        serde_json::json!({
            "frames": {"type": "int", "value": frame_count},
            "obligations": {"type": "int", "value": obligations},
            "currentLevel": {"type": "int", "value": current_level},
            "result": {"type": "string", "value": result},
            "lemmaCount": {"type": "int", "value": Self::usize_to_i64(lemma_count)},
            "activePredicate": {"type": "int", "value": active_pred},
            "activeLevel": {"type": "int", "value": active_lvl},
            "obligationDepth": {"type": "int", "value": ob_depth},
        })
    }

    /// Build a snapshot with no active obligation context.
    fn pdr_trace_snapshot_without_active(&self, result: &str) -> serde_json::Value {
        let frame_count = Self::usize_to_i64(self.frames.len());
        let obligations = Self::usize_to_i64(self.obligations_len());
        let current_level = match self.tracing.query_level {
            Some(level) => Self::usize_to_i64(level),
            None => Self::usize_to_i64(self.frames.len().saturating_sub(1)),
        };
        let lemma_count: usize = self.frames.iter().map(|f| f.lemmas.len()).sum();

        serde_json::json!({
            "frames": {"type": "int", "value": frame_count},
            "obligations": {"type": "int", "value": obligations},
            "currentLevel": {"type": "int", "value": current_level},
            "result": {"type": "string", "value": result},
            "lemmaCount": {"type": "int", "value": Self::usize_to_i64(lemma_count)},
            "activePredicate": {"type": "int", "value": -1_i64},
            "activeLevel": {"type": "int", "value": -1_i64},
            "obligationDepth": {"type": "int", "value": 0_i64},
        })
    }

    /// Emit a single PDR trace step when trace output is enabled.
    ///
    /// `active_pob` provides obligation context for BlockObligation and LearnLemma actions.
    /// Pass `None` for non-obligation actions.
    pub(in crate::pdr::solver) fn pdr_trace_step(
        &self,
        result: &str,
        action: Option<&str>,
        active_pob: Option<&ProofObligation>,
    ) {
        if let Some(ref writer) = self.tracing.tla_trace {
            writer.write_step(self.pdr_trace_snapshot(result, active_pob), action);
        }
    }

    /// Emit a reason-bearing conservative-failure trace step.
    ///
    /// Uses a spec-compatible action name and attaches failure telemetry so Unknown
    /// exits can be triaged without parsing stderr.
    pub(in crate::pdr::solver) fn pdr_trace_conservative_fail(
        &self,
        reason: &'static str,
        detail: serde_json::Value,
        active_pob: Option<&ProofObligation>,
    ) {
        let Some(ref writer) = self.tracing.tla_trace else {
            return;
        };

        let has_active_obligation = active_pob.is_some() || self.tracing.active_pob.is_some();
        let (action, state) = if has_active_obligation {
            (
                "BlockObligation",
                self.pdr_trace_snapshot("Running", active_pob),
            )
        } else {
            (
                "PropagateLemmas",
                self.pdr_trace_snapshot_without_active("Running"),
            )
        };

        let entry_failure_total: usize = self
            .telemetry
            .entry_inductive_failure_counts
            .values()
            .copied()
            .sum();
        let cegar_total: usize = self.telemetry.entry_cegar_discharge_outcomes.iter().sum();
        let telemetry = serde_json::json!({
            "failure": {
                "reason": reason,
                "detail": detail,
            },
            "counters": {
                "iterations": self.iterations,
                "sat_no_cube_events": self.telemetry.sat_no_cube_events,
                "interpolation_attempts": self.telemetry.interpolation_stats.attempts,
                "interpolation_all_failed": self.telemetry.interpolation_stats.all_failed,
                "entry_inductive_failure_total": entry_failure_total,
                "entry_cegar_discharge_total": cegar_total,
                "consecutive_unlearnable_failures": self.verification.consecutive_unlearnable,
                "total_verification_unknowns": self.verification.total_unknowns,
                "total_model_verification_failures": self.verification.total_model_failures,
            },
        });
        writer.write_step_with_telemetry(state, Some(action), Some(telemetry));
    }

    /// Flush the trace file (no-op when trace output is disabled).
    pub(in crate::pdr::solver) fn finish_pdr_tla_trace(&self) {
        if let Some(ref writer) = self.tracing.tla_trace {
            let _ = writer.finish();
        }
    }

    /// Build a telemetry payload from accumulated solver diagnostics.
    ///
    /// Captures interpolation cascade stats, SAT-no-cube events, and
    /// entry-inductiveness failure reasons as structured JSON for offline
    /// triage (#4697).
    fn build_telemetry_payload(&self) -> serde_json::Value {
        // Interpolation cascade stats (#2450).
        let interp = &self.telemetry.interpolation_stats;
        let interpolation = serde_json::json!({
            "attempts": interp.attempts,
            "golem_sat_successes": interp.golem_sat_successes,
            "n1_per_clause_successes": interp.n1_per_clause_successes,
            "lia_farkas_successes": interp.lia_farkas_successes,
            "syntactic_farkas_successes": interp.syntactic_farkas_successes,
            "iuc_farkas_successes": interp.iuc_farkas_successes,
            "golem_a_unsat_skips": interp.golem_a_unsat_skips,
            "all_failed": interp.all_failed,
        });

        // Entry-inductiveness failure histogram (#4695).
        let entry_failures: serde_json::Map<String, serde_json::Value> = self
            .telemetry
            .entry_inductive_failure_counts
            .iter()
            .map(|(reason, &count)| (reason.to_string(), serde_json::json!(count)))
            .collect();

        // Entry-CEGAR discharge outcome histogram (#4697).
        let [reachable, unreachable, unknown] = self.telemetry.entry_cegar_discharge_outcomes;
        let cegar_discharges = serde_json::json!({
            "reachable": reachable,
            "unreachable": unreachable,
            "unknown": unknown,
        });

        serde_json::json!({
            "interpolation": interpolation,
            "sat_no_cube_events": self.telemetry.sat_no_cube_events,
            "entry_inductive_failures": entry_failures,
            "entry_cegar_discharges": cegar_discharges,
        })
    }

    /// Emit the terminal action for a solver result and flush the trace.
    ///
    /// The terminal step includes a `telemetry` payload with accumulated
    /// interpolation stats, SAT-no-cube counts, and entry-inductiveness
    /// failure reasons for offline Unknown-outcome triage (#4697).
    pub(in crate::pdr::solver) fn finish_with_result_trace(&self, result: PdrResult) -> PdrResult {
        let (result_str, action) = match &result {
            PdrResult::Safe(_) => ("Safe", "DeclareSafe"),
            PdrResult::Unsafe(_) => ("Unsafe", "DeclareUnsafe"),
            PdrResult::Unknown | PdrResult::NotApplicable => ("Unknown", "DeclareUnknown"),
        };
        // Emit terminal step with telemetry payload.
        if let Some(ref writer) = self.tracing.tla_trace {
            let state = self.pdr_trace_snapshot(result_str, None);
            let telemetry = self.build_telemetry_payload();
            writer.write_step_with_telemetry(state, Some(action), Some(telemetry));
        }
        tracing::info!(
            action,
            result = result_str,
            frames = self.frames.len(),
            "PDR solver terminated"
        );
        // Print interpolation telemetry at solve end (#2450)
        if self.config.verbose && self.telemetry.interpolation_stats.attempts > 0 {
            safe_eprintln!(
                "PDR: Interpolation stats: {}",
                self.telemetry.interpolation_stats.summary()
            );
        }
        // Export learned lemmas to the sequential lemma cache (#7919).
        if matches!(result, PdrResult::Unknown) {
            if let Some(ref cache) = self.config.lemma_cache {
                let pool = self.export_lemmas();
                if !pool.is_empty() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Exported {} lemmas to sequential LemmaCache (#7919)",
                            pool.len()
                        );
                    }
                    cache.merge(&pool);
                }
            }
        }

        self.finish_pdr_tla_trace();
        result
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#[test]
fn test_preprocess_propagate_checks_always_guard_empty_clause() {
    let source = include_str!("config_preprocess.rs");
    let start = source
        .find("pub(super) fn preprocess(&mut self) -> bool {")
        .expect("preprocess definition must exist");
    let end = source[start..]
        .find("/// Helper: count the number of fixed (assigned at level 0) variables")
        .map(|offset| start + offset)
        .expect("preprocess terminator must exist");
    let preprocess = &source[start..end];

    const CALL: &str = "self.propagate().is_some()";
    for (offset, _) in preprocess.match_indices(CALL) {
        let line_start = preprocess[..offset].rfind('\n').map_or(0, |i| i + 1);
        let line_end = preprocess[offset..]
            .find('\n')
            .map_or(preprocess.len(), |i| offset + i);
        let line = &preprocess[line_start..line_end];

        assert!(
            line.contains("self.has_empty_clause ||"),
            "preprocess propagate check must include has_empty_clause guard: {line}",
        );
    }
}

/// Regression guard: preprocess() must NOT disable inprocessing techniques
/// based on LRAT mode. The sole authority for LRAT technique disabling is
/// InprocessingControls::with_proof_overrides() in inproc_control.rs (#4569).
///
/// Note: preprocess() legitimately reads `self.cold.lrat_enabled` for conditional
/// behavior (probe path selection, subsumption hint collection). Only blanket
/// `inproc_ctrl.*.enabled = false` under an LRAT guard is forbidden.
#[test]
fn test_preprocess_has_no_manual_lrat_overrides() {
    let source = include_str!("config_preprocess.rs");
    // Scope: preprocess function body only (before the test module)
    let fn_start = source
        .find("fn preprocess(")
        .expect("preprocess function must exist");
    let test_mod = source.find("#[cfg(test)]").unwrap_or(source.len());
    let fn_body = &source[fn_start..test_mod];

    // The anti-pattern: any inproc_ctrl technique disabled under an LRAT guard.
    // Build technique names dynamically to avoid include_str! self-matching.
    let lrat_disabled_techniques = ["congruence", "sweep", "factor"];
    for tech in &lrat_disabled_techniques {
        let pattern = format!("self.inproc_ctrl.{tech}.enabled = false");
        assert!(
            !fn_body.contains(&pattern),
            "preprocess() must not manually disable {tech} — \
             use InprocessingControls::with_proof_overrides() (#4569)",
        );
    }
}

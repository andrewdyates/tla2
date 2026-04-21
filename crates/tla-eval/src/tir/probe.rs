// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};

use tla_value::error::EvalResult;
use tla_value::Value;

/// Hidden integration-test support for proving that TIR eval actually ran.
///
/// Part of #3194: the resolved-name canaries need a TIR-specific observable so
/// a silent AST fallback no longer leaves the suite green.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[doc(hidden)]
pub struct TirEvalProbeCounts {
    pub expr_evals: usize,
    pub named_op_evals: usize,
}

#[doc(hidden)]
pub const TIR_CLOSURE_BODY_PROBE_LABEL: &str = "__tir_closure_body__";

/// Detailed result for leaf-level TIR expression attempts.
///
/// Hidden integration support for leaf parity debugging in `tla-check`.
/// Unlike `try_eval_expr()`, this preserves TIR eval errors so callers can
/// compare them against the AST path before deciding whether to fall back.
#[derive(Debug)]
#[doc(hidden)]
pub enum TirExprEvalAttempt {
    Unsupported,
    Evaluated(EvalResult<Value>),
}

static TIR_EVAL_PROBE_ENABLED: AtomicBool = AtomicBool::new(false);
static TIR_EVAL_PROBE: OnceLock<Mutex<BTreeMap<String, TirEvalProbeCounts>>> = OnceLock::new();

fn tir_eval_probe() -> &'static Mutex<BTreeMap<String, TirEvalProbeCounts>> {
    TIR_EVAL_PROBE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

pub(super) fn record_expr_eval(label: &str) {
    if !TIR_EVAL_PROBE_ENABLED.load(Ordering::Relaxed) {
        return;
    }
    let mut probe = tir_eval_probe()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    probe.entry(label.to_string()).or_default().expr_evals += 1;
}

pub(super) fn record_named_op_eval(name: &str) {
    if !TIR_EVAL_PROBE_ENABLED.load(Ordering::Relaxed) {
        return;
    }
    let mut probe = tir_eval_probe()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    probe.entry(name.to_string()).or_default().named_op_evals += 1;
}

pub(crate) fn record_closure_body_eval() {
    record_expr_eval(TIR_CLOSURE_BODY_PROBE_LABEL);
}

#[doc(hidden)]
pub fn enable_tir_eval_probe() {
    TIR_EVAL_PROBE_ENABLED.store(true, Ordering::Relaxed);
}

#[must_use]
#[doc(hidden)]
pub fn tir_eval_probe_snapshot() -> BTreeMap<String, TirEvalProbeCounts> {
    tir_eval_probe()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone()
}

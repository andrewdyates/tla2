// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Portfolio configuration and result types.

use crate::bmc::BmcConfig;
use crate::cancellation::CancellationToken;
use crate::cegar::{CegarConfig, CegarResult};
use crate::dar::DarConfig;
use crate::decomposition::DecompositionConfig;
use crate::engine_result::ChcEngineResult;
use crate::imc::ImcConfig;
use crate::kind::KindConfig;
use crate::lawi::LawiConfig;
use crate::pdkind::PdkindConfig;
use crate::pdr::{
    Counterexample, CounterexampleStep, InvariantModel, PdrConfig, PredicateInterpretation,
};
use crate::tpa::{TpaConfig, TpaResult};
use crate::trl::TrlConfig;
use crate::LemmaHint;
use rustc_hash::FxHashMap;
use std::time::Duration;

/// Configuration for an individual engine
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum EngineConfig {
    /// PDR engine with configuration
    Pdr(PdrConfig),
    /// BMC engine with configuration
    Bmc(BmcConfig),
    /// PDKIND engine with configuration
    Pdkind(PdkindConfig),
    /// TPA engine with configuration
    Tpa(TpaConfig),
    /// TRL engine with configuration
    Trl(TrlConfig),
    /// Kind engine with configuration (forward/backward k-induction)
    Kind(KindConfig),
    /// Decomposition engine with configuration
    /// Decomposes multi-predicate problems into SCCs and solves sequentially
    Decomposition(DecompositionConfig),
    /// IMC engine with configuration
    Imc(ImcConfig),
    /// LAWI engine with configuration
    Lawi(LawiConfig),
    /// DAR engine with configuration (Dual Approximated Reachability)
    Dar(DarConfig),
    /// CEGAR engine with configuration
    Cegar(CegarConfig),
}

impl EngineConfig {
    /// Create a PDKIND engine with default configuration.
    ///
    /// `PdkindConfig` is crate-internal; this is the public way to add a
    /// PDKIND engine to a portfolio.
    pub fn pdkind_default() -> Self {
        Self::Pdkind(PdkindConfig::default())
    }

    /// Human-readable engine name for diagnostics.
    pub(crate) fn name(&self) -> &'static str {
        match self {
            Self::Pdr(_) => "PDR",
            Self::Bmc(_) => "BMC",
            Self::Pdkind(_) => "PDKIND",
            Self::Imc(_) => "IMC",
            Self::Lawi(_) => "LAWI",
            Self::Dar(_) => "DAR",
            Self::Tpa(_) => "TPA",
            Self::Trl(_) => "TRL",
            Self::Kind(_) => "Kind",
            Self::Decomposition(_) => "Decomposition",
            Self::Cegar(_) => "CEGAR",
        }
    }

    /// Create the Unknown EngineResult for this engine type.
    ///
    /// Used for panic recovery (#2728): when an engine panics, we wrap it as Unknown
    /// using the correct variant so downstream logging and validation correctly
    /// attributes the result. This is an exhaustive match — adding a new EngineConfig
    /// variant forces updating this method (compile error).
    pub(super) fn unknown_result(&self) -> EngineResult {
        match self {
            Self::Pdr(_)
            | Self::Bmc(_)
            | Self::Trl(_)
            | Self::Imc(_)
            | Self::Lawi(_)
            | Self::Dar(_)
            | Self::Kind(_)
            | Self::Decomposition(_) => {
                EngineResult::Unified(ChcEngineResult::Unknown, self.name())
            }
            Self::Pdkind(_) => EngineResult::Unified(ChcEngineResult::Unknown, "PDKIND"),
            Self::Tpa(_) => EngineResult::Tpa(TpaResult::Unknown),
            Self::Cegar(_) => EngineResult::Cegar(CegarResult::Unknown),
        }
    }

    /// Inject a cancellation token into the engine config.
    ///
    /// PDR stores the token directly; all other engines store it in `base`.
    pub(super) fn inject_cancellation_token(&mut self, token: CancellationToken) {
        match self {
            Self::Pdr(c) => c.cancellation_token = Some(token),
            Self::Bmc(c) => c.base.cancellation_token = Some(token),
            Self::Pdkind(c) => c.base.cancellation_token = Some(token),
            Self::Imc(c) => c.base.cancellation_token = Some(token),
            Self::Lawi(c) => c.base.cancellation_token = Some(token),
            Self::Dar(c) => c.base.cancellation_token = Some(token),
            Self::Tpa(c) => c.base.cancellation_token = Some(token),
            Self::Trl(c) => c.base.cancellation_token = Some(token),
            Self::Kind(c) => c.base.cancellation_token = Some(token),
            Self::Decomposition(c) => c.base.cancellation_token = Some(token),
            Self::Cegar(c) => c.base.cancellation_token = Some(token),
        }
    }

    /// Inject a sequential lemma cache into PDR engine configs (#7919).
    pub(super) fn inject_lemma_cache(&mut self, cache: &crate::lemma_cache::LemmaCache) {
        if let Self::Pdr(c) = self {
            c.lemma_cache = Some(cache.clone());
        }
    }

    /// Seed a PDR engine with accumulated lemmas from the cache (#7919).
    pub(super) fn seed_from_lemma_cache(&mut self, cache: &crate::lemma_cache::LemmaCache) {
        if let Self::Pdr(c) = self {
            let pool = cache.snapshot();
            if !pool.is_empty() {
                c.lemma_hints = Some(pool);
            }
        }
    }

    /// Inject a cooperative blackboard and engine index into the engine config.
    ///
    /// PDR and CEGAR engines use the blackboard for sharing learned
    /// lemmas/predicates. Other engines silently ignore it.
    pub(super) fn inject_blackboard(
        &mut self,
        blackboard: std::sync::Arc<crate::blackboard::SharedBlackboard>,
        engine_idx: usize,
    ) {
        match self {
            Self::Pdr(c) => {
                c.blackboard = Some(blackboard);
                c.engine_idx = engine_idx;
            }
            Self::Cegar(c) => {
                c.blackboard = Some(blackboard);
                c.engine_idx = engine_idx;
            }
            _ => {}
        }
    }

    /// Ensure a cancellation token exists, creating one if absent.
    /// Returns a clone of the token for the caller to use (e.g. to cancel).
    pub(super) fn ensure_cancellation_token(&mut self) -> CancellationToken {
        match self {
            Self::Pdr(c) => c
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Bmc(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Pdkind(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Imc(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Lawi(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Dar(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Tpa(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Trl(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Kind(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Decomposition(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
            Self::Cegar(c) => c
                .base
                .cancellation_token
                .get_or_insert_with(CancellationToken::new)
                .clone(),
        }
    }
}

/// Portfolio solver configuration
#[derive(Debug, Clone)]
pub struct PortfolioConfig {
    /// Engines to run (order matters for sequential mode)
    pub(crate) engines: Vec<EngineConfig>,
    /// Run engines in parallel (true) or sequential (false)
    pub(crate) parallel: bool,
    /// Timeout per engine in sequential mode (None = no timeout).
    ///
    /// When this timeout expires, the current engine is cooperatively cancelled
    /// (via a cancellation token) and treated as returning `Unknown`; the
    /// portfolio then proceeds to the next engine.
    pub(crate) timeout: Option<Duration>,
    /// Overall timeout for parallel mode (None = no timeout)
    /// When specified, portfolio will return Unknown if no engine produces
    /// a definitive result within this duration.
    pub(crate) parallel_timeout: Option<Duration>,
    /// Enable verbose output
    pub(crate) verbose: bool,
    /// Enable runtime validation of engine results (default: false).
    /// When true, every Safe/Unsafe result is re-verified by a fresh solver.
    /// When false, engine results are accepted directly. Use for debugging.
    pub(crate) validate: bool,
    /// Enable preprocessing (clause inlining, etc.)
    /// Default: true - ClauseInliner is applied before solving.
    pub(crate) enable_preprocessing: bool,
}

impl Default for PortfolioConfig {
    fn default() -> Self {
        // Delegate to EngineSelector::default_engines() for the canonical
        // engine roster (#7946: one engine-policy source of truth).
        Self {
            engines: super::selector::EngineSelector::default_engines(),
            parallel: true,
            timeout: None,
            parallel_timeout: None,
            verbose: false,
            validate: false,
            enable_preprocessing: true,
        }
    }
}

impl PortfolioConfig {
    /// Create a config with just TPA
    #[cfg(test)]
    pub(crate) fn tpa_only(config: TpaConfig) -> Self {
        Self {
            engines: vec![EngineConfig::Tpa(config)],
            parallel: false,
            timeout: None,
            parallel_timeout: None,
            verbose: false,
            validate: false,
            enable_preprocessing: false,
        }
    }

    /// Get the configured engines.
    pub fn engines(&self) -> &[EngineConfig] {
        &self.engines
    }

    /// Create a portfolio config with the given engines and default settings.
    pub fn with_engines(engines: Vec<EngineConfig>) -> Self {
        Self {
            engines,
            parallel: true,
            timeout: None,
            parallel_timeout: None,
            verbose: false,
            validate: false,
            enable_preprocessing: true,
        }
    }

    /// Set parallel mode.
    pub fn parallel(mut self, parallel: bool) -> Self {
        self.parallel = parallel;
        self
    }

    /// Set per-engine timeout (sequential mode).
    pub fn timeout(mut self, timeout: Option<Duration>) -> Self {
        self.timeout = timeout;
        self
    }

    /// Set overall parallel timeout.
    pub fn parallel_timeout(mut self, timeout: Option<Duration>) -> Self {
        self.parallel_timeout = timeout;
        self
    }

    /// Set verbose output.
    pub fn verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Set preprocessing (clause inlining, etc.).
    pub fn preprocessing(mut self, enable: bool) -> Self {
        self.enable_preprocessing = enable;
        self
    }

    /// Set user hints on all PDR engines in the portfolio.
    ///
    /// This helper ensures hints are applied to ALL PDR configs, avoiding
    /// partial application when the default portfolio has multiple PDR variants.
    ///
    /// # Example
    /// ```text
    /// let mut config = PortfolioConfig::default();
    /// config.set_pdr_user_hints(vec![hint1, hint2]);
    /// ```
    pub fn set_pdr_user_hints(&mut self, hints: Vec<LemmaHint>) {
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.user_hints = hints.clone();
            }
        }
    }

    /// Apply runtime hint providers to all PDR engines in the portfolio.
    ///
    /// Similar to [`set_pdr_user_hints`](Self::set_pdr_user_hints), but for
    /// dynamic `LemmaHintProvider` implementations instead of pre-computed hints.
    pub fn set_pdr_user_hint_providers(&mut self, providers: crate::lemma_hints::HintProviders) {
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.user_hint_providers = providers.clone();
            }
        }
    }

    /// Seed all PDR engines with a cross-engine lemma pool (#7919).
    ///
    /// Converts the pool's learned lemmas into `PdrConfig::lemma_hints` on each
    /// PDR engine in the portfolio. This is the entry point for transferring
    /// lemmas from a prior non-inlined PDR stage into the portfolio's engines.
    pub fn set_pdr_lemma_pool(&mut self, pool: &crate::lemma_pool::LemmaPool) {
        if pool.is_empty() {
            return;
        }
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.lemma_hints = Some(pool.clone());
            }
        }
    }

    /// Cap PDR escalation and remove Kind for DT problems (#7930).
    pub fn apply_dt_guards(&mut self, max_escalation: usize) {
        for engine in &mut self.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                pdr.max_escalation_level = max_escalation;
            }
        }
        self.engines.retain(|e| !matches!(e, EngineConfig::Kind(_)));
    }
}

/// Portfolio result type — alias for the unified ChcEngineResult (#2791).
pub type PortfolioResult = ChcEngineResult;

// From impls for unconverted engines (will be removed as each engine is converted to ChcEngineResult)
// PDR, BMC, TRL already return ChcEngineResult directly.

// From<PdkindResult> removed: PdkindResult is now a type alias for ChcEngineResult,
// so conversion is identity. PDKind conversion logic lives in pdkind.rs convert_raw_result().

impl From<TpaResult> for PortfolioResult {
    fn from(result: TpaResult) -> Self {
        match result {
            TpaResult::Safe {
                invariant,
                power: _,
            } => {
                let mut model = InvariantModel::new();
                if let Some(inv_expr) = invariant {
                    let vars = inv_expr.vars();
                    model.set(
                        crate::PredicateId(0),
                        PredicateInterpretation::new(vars, inv_expr),
                    );
                }
                Self::Safe(model)
            }
            TpaResult::Unsafe { steps, trace: _ } => {
                let step_count = steps.min(100) as usize;
                let cex_steps = (0..=step_count)
                    .map(|_| CounterexampleStep {
                        predicate: crate::PredicateId(0),
                        assignments: FxHashMap::default(),
                    })
                    .collect();
                Self::Unsafe(Counterexample {
                    steps: cex_steps,
                    witness: None,
                })
            }
            TpaResult::Unknown => Self::Unknown,
        }
    }
}

impl From<CegarResult> for PortfolioResult {
    fn from(result: CegarResult) -> Self {
        match result {
            CegarResult::Safe(model) => Self::Safe(model),
            CegarResult::Unsafe(cex) => {
                let steps = cex
                    .trace
                    .iter()
                    .map(|(_, state)| {
                        let predicate =
                            state.as_ref().map_or(crate::PredicateId(0), |s| s.relation);
                        CounterexampleStep {
                            predicate,
                            assignments: FxHashMap::default(),
                        }
                    })
                    .collect();
                Self::Unsafe(Counterexample {
                    steps,
                    witness: None,
                })
            }
            CegarResult::Unknown => Self::Unknown,
        }
    }
}

/// Internal message for engine results.
/// Engines that have been converted to ChcEngineResult use the Unified variant.
/// Unconverted engines still use their dedicated variants.
#[derive(Debug, Clone)]
pub(super) enum EngineResult {
    /// PDR, BMC, TRL, IMC, Kind, PDKind, Decomposition — return ChcEngineResult
    Unified(ChcEngineResult, &'static str),
    Tpa(TpaResult),
    Cegar(CegarResult),
}

impl EngineResult {
    /// Short summary string for verbose logging.
    pub(super) fn summary(&self) -> &'static str {
        match self {
            Self::Unified(r, _) => match r {
                ChcEngineResult::Safe(_) => "Safe",
                ChcEngineResult::Unsafe(_) => "Unsafe",
                ChcEngineResult::Unknown => "Unknown",
                ChcEngineResult::NotApplicable => "NotApplicable",
            },
            Self::Tpa(r) => match r {
                TpaResult::Safe { .. } => "Safe",
                TpaResult::Unsafe { .. } => "Unsafe",
                TpaResult::Unknown => "Unknown",
            },
            Self::Cegar(r) => match r {
                CegarResult::Safe(_) => "Safe",
                CegarResult::Unsafe(_) => "Unsafe",
                CegarResult::Unknown => "Unknown",
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_apply_dt_guards_caps_pdr_escalation() {
        let mut config = PortfolioConfig::default();
        // Default should have PDR with max_escalation_level=3
        let pdr_count = config
            .engines
            .iter()
            .filter(|e| matches!(e, EngineConfig::Pdr(_)))
            .count();
        assert!(
            pdr_count >= 2,
            "default portfolio should have at least 2 PDR engines"
        );

        config.apply_dt_guards(0);

        for engine in &config.engines {
            if let EngineConfig::Pdr(pdr) = engine {
                assert_eq!(
                    pdr.max_escalation_level, 0,
                    "PDR escalation should be capped to 0"
                );
            }
        }
    }

    #[test]
    fn test_apply_dt_guards_removes_kind() {
        let mut config = PortfolioConfig::default();
        let has_kind_before = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Kind(_)));
        assert!(has_kind_before, "default portfolio should include Kind");

        config.apply_dt_guards(0);

        let has_kind_after = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Kind(_)));
        assert!(
            !has_kind_after,
            "apply_dt_guards should remove Kind engines"
        );
    }
}

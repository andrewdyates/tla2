// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing engine sub-struct for hot/cold field separation (#5090).
//!
//! Groups cold inprocessing engine instances into a single struct so the
//! Solver's hot BCP fields are not intermixed with cold engine state.
//! All fields are accessed only during inprocessing rounds, not during
//! BCP or conflict analysis.

use crate::bce::BCE;
use crate::bve::BVE;
use crate::cce::Cce;
use crate::condition::Conditioning;
use crate::congruence::CongruenceClosure;
use crate::decompose::Decompose;
use crate::factor::Factor;
use crate::gates::GateExtractor;
use crate::htr::HTR;
use crate::kitten::Kitten;
use crate::reconstruct::ReconstructionStack;
use crate::subsume::Subsumer;
use crate::sweep::Sweeper;
use crate::transred::TransRed;
use crate::vivify::Vivifier;

/// Cold inprocessing engine state, separated from the Solver's hot BCP fields.
///
/// These fields are only accessed during inprocessing/preprocessing rounds.
/// Grouping them reduces cognitive overhead (Solver has ~140 fields) and
/// provides a clear hot/cold boundary for cache analysis.
///
/// Reference: CaDiCaL groups these as separate subsystem objects; Z4's flat
/// struct intermixed them with BCP state, polluting field adjacency analysis.
pub(crate) struct InprocessingEngines {
    /// Vivification engine
    pub vivifier: Vivifier,
    /// Subsumption engine
    pub subsumer: Subsumer,
    /// Failed literal prober
    pub prober: crate::probe::Prober,
    /// Bounded Variable Elimination
    pub bve: BVE,
    /// Blocked Clause Elimination
    pub bce: BCE,
    /// Covered Clause Elimination (ACCE)
    pub cce: Cce,
    /// Conditioning (Globally Blocked Clause Elimination)
    pub conditioning: Conditioning,
    /// Decompose (SCC-based Equivalent Literal Substitution)
    pub decompose_engine: Decompose,
    /// Factorization (CaDiCaL factor.cpp)
    pub factor_engine: Factor,
    /// Transitive Reduction
    pub transred_engine: TransRed,
    /// Hyper-Ternary Resolution
    pub htr: HTR,
    /// Gate Extraction
    pub gate_extractor: GateExtractor,
    /// Congruence Closure (gate-based equivalence detection)
    pub congruence: CongruenceClosure,
    /// SAT Sweeping
    pub sweeper: Sweeper,
    /// Dedicated kitten instance for BVE definition extraction.
    pub definition_kitten: Kitten,
    /// Model Reconstruction
    pub reconstruction: ReconstructionStack,
}

impl InprocessingEngines {
    /// Create all inprocessing engines for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        let mut definition_kitten = Kitten::new();
        definition_kitten.enable_antecedent_tracking();
        Self {
            vivifier: Vivifier::new(),
            subsumer: Subsumer::new(num_vars),
            prober: crate::probe::Prober::new(num_vars),
            bve: BVE::new(num_vars),
            bce: BCE::new(num_vars),
            cce: Cce::new(num_vars),
            conditioning: Conditioning::new(num_vars),
            decompose_engine: Decompose::new(num_vars),
            factor_engine: Factor::new(num_vars),
            transred_engine: TransRed::new(num_vars),
            htr: HTR::new(num_vars),
            gate_extractor: GateExtractor::new(num_vars),
            congruence: CongruenceClosure::new(num_vars),
            sweeper: Sweeper::new(num_vars),
            definition_kitten,
            reconstruction: ReconstructionStack::new(),
        }
    }

    /// Reset all engine-internal watermarks to their initial values.
    ///
    /// MUST be called when `search_ticks` or `num_propagations` is reset
    /// (i.e., in `reset_search_state()`). Without this, the `saturating_sub`
    /// effort computation in each engine yields 0 until the tick/propagation
    /// counter re-accumulates past the stale watermark — starving the
    /// technique of budget for the entire second solve (#8159).
    ///
    /// Centralizes the reset so future engine authors have a single place
    /// to add their watermark reset line.
    pub(crate) fn reset_watermarks(&mut self) {
        self.prober.set_last_search_ticks(0);
        // HTR uses Option<u64>: None means "first call uses INIT budget".
        // Resetting to None (not Some(0)) preserves first-call behavior.
        self.htr.reset_last_search_ticks();
        self.transred_engine.set_last_propagations(0);
    }

    /// Resize all engines to accommodate `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        self.subsumer.ensure_num_vars(num_vars);
        self.prober.ensure_num_vars(num_vars);
        self.bve.ensure_num_vars(num_vars);
        self.bce.ensure_num_vars(num_vars);
        self.cce.ensure_num_vars(num_vars);
        self.decompose_engine.ensure_num_vars(num_vars);
        self.factor_engine.ensure_num_vars(num_vars);
        self.transred_engine.ensure_num_vars(num_vars);
        self.htr.ensure_num_vars(num_vars);
        self.gate_extractor.ensure_num_vars(num_vars);
        self.congruence.ensure_num_vars(num_vars);
        self.sweeper.ensure_num_vars(num_vars);
        self.conditioning.ensure_num_vars(num_vars);
    }
}

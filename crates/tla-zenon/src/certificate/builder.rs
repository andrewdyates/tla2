// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Certificate builder state for generating linear step sequences.

use std::collections::HashMap;
use tla_cert::{CertificateStep, Formula as CertFormula, Justification, StepId};

/// State for certificate generation.
pub(super) struct CertificateBuilder {
    /// Next step ID to assign.
    next_id: StepId,
    /// Generated steps.
    pub(super) steps: Vec<CertificateStep>,
    /// Map from formulas to their step IDs (for referencing previously proven facts).
    formula_to_step: HashMap<CertFormula, StepId>,
}

impl CertificateBuilder {
    pub(super) fn new() -> Self {
        Self {
            next_id: 0,
            steps: Vec::new(),
            formula_to_step: HashMap::new(),
        }
    }

    /// Add a step and return its ID.
    pub(super) fn add_step(
        &mut self,
        formula: CertFormula,
        justification: Justification,
    ) -> StepId {
        let id = self.next_id;
        self.next_id += 1;

        // Record this formula's step ID for later reference
        self.formula_to_step.insert(formula.clone(), id);

        self.steps.push(CertificateStep {
            id,
            formula,
            justification,
        });

        id
    }

    /// Look up a formula's step ID.
    pub(super) fn lookup(&self, formula: &CertFormula) -> Option<StepId> {
        self.formula_to_step.get(formula).copied()
    }
}

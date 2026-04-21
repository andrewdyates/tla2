// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Non-linear Real Arithmetic (NRA) solving.
//!
//! Uses model-based incremental linearization, delegating to the LRA simplex
//! solver for the linear relaxation. Sign lemmas and tangent plane lemmas
//! refine the linear model until the nonlinear constraints are satisfied.

use z4_nra::NraSolver;

use super::super::Executor;
use crate::executor_types::Result;
use crate::executor_types::SolveResult;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

impl Executor {
    pub(in crate::executor) fn solve_nra(&mut self) -> Result<SolveResult> {
        solve_incremental_theory_pipeline!(self,
            tag: "NRA",
            create_theory: NraSolver::new(&self.ctx.terms),
            extract_models: |theory| TheoryModels {
                lra: Some(theory.extract_model()),
                ..TheoryModels::default()
            },
            track_theory_stats: true,
            set_unknown_on_error: true
        )
    }
}

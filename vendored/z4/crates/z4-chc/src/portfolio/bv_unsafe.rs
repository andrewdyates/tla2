// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::Counterexample;

impl PortfolioSolver {
    pub(super) fn confirm_bv_abstracted_unsafe(
        &self,
        cex: &Counterexample,
        idx: usize,
        engine_name: &str,
    ) -> Option<PortfolioResult> {
        match self.validate_unsafe(cex) {
            ValidationResult::Valid => Some(PortfolioResult::Unsafe(
                self.back_translator.translate_invalidity(cex.clone()),
            )),
            ValidationResult::Invalid(reason) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) Unsafe rejected \
                         during original-domain confirmation: {}",
                        idx,
                        engine_name,
                        reason
                    );
                }
                None
            }
        }
    }
}

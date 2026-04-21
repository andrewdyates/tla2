// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NIA sign consistency checking on `NiaSolver`.

use z4_core::nonlinear;

use super::*;

impl NiaSolver<'_> {
    /// Check if a monomial's value is consistent with its factors
    pub(crate) fn check_monomial_consistency(&self, mon: &Monomial) -> bool {
        let mut product = BigRational::one();
        for &var in &mon.vars {
            if let Some(val) = self.var_value(var) {
                product *= val;
            } else {
                return true;
            }
        }
        if let Some(aux_val) = self.var_value(mon.aux_var) {
            aux_val == product
        } else {
            true
        }
    }

    /// Check sign consistency for all monomials using constraint-based approach.
    pub(crate) fn check_sign_consistency(&self) -> Option<Vec<TheoryLit>> {
        if self.debug {
            safe_eprintln!("[NIA] check_sign_consistency: {} monomials, {} sign_constraints, {} var_sign_constraints",
                self.monomials.len(), self.sign_constraints.len(), self.var_sign_constraints.len());
            for (vars, constraints) in &self.sign_constraints {
                safe_eprintln!(
                    "[NIA]   monomial {:?} has {} constraints: {:?}",
                    vars,
                    constraints.len(),
                    constraints
                );
            }
            for (var, constraints) in &self.var_sign_constraints {
                safe_eprintln!(
                    "[NIA]   var {:?} has {} constraints: {:?}",
                    var,
                    constraints.len(),
                    constraints
                );
            }
        }

        let mut sorted_sign: Vec<_> = self.sign_constraints.iter().collect();
        sorted_sign.sort_by(|(a, _), (b, _)| a.cmp(b));
        for (vars, constraints) in sorted_sign {
            let Some(mon) = self.monomials.get(vars) else {
                if self.debug {
                    safe_eprintln!("[NIA] No monomial found for vars {:?}", vars);
                }
                continue;
            };
            if !mon.is_binary() {
                continue;
            }

            let x = mon.x()?;
            let y = mon.y()?;
            let x_signs = self.var_sign_constraints.get(&x);
            let y_signs = self.var_sign_constraints.get(&y);

            if self.debug {
                safe_eprintln!(
                    "[NIA] Checking monomial {:?}: x={:?} y={:?} x_signs={:?} y_signs={:?}",
                    vars,
                    x,
                    y,
                    x_signs,
                    y_signs
                );
            }

            let x_sign = nonlinear::sign_from_constraints(x_signs);
            let y_sign = nonlinear::sign_from_constraints(y_signs);

            if let (Some(xs), Some(ys)) = (x_sign, y_sign) {
                let expected_sign = nonlinear::product_sign(&[xs, ys]);
                if self.debug {
                    safe_eprintln!(
                        "[NIA] x_sign={}, y_sign={}, expected_sign={}",
                        xs,
                        ys,
                        expected_sign
                    );
                }
                for (constraint, _assertion) in constraints {
                    if nonlinear::sign_contradicts(*constraint, expected_sign) {
                        if self.debug {
                            safe_eprintln!("[NIA] Sign conflict: x_sign={}, y_sign={}, expected_prod={}, constraint={:?}", xs, ys, expected_sign, constraint);
                        }
                        return Some(
                            self.asserted
                                .iter()
                                .map(|(term, val)| TheoryLit::new(*term, *val))
                                .collect(),
                        );
                    }
                }
            }
        }
        None
    }

    /// Extract sign constraint from a comparison with zero
    pub(crate) fn extract_sign_constraint(
        &self,
        term: TermId,
        value: bool,
    ) -> Option<(TermId, SignConstraint)> {
        nonlinear::extract_sign_constraint(self.terms, term, value)
    }

    /// Record sign constraint for a subject term (variable or monomial)
    pub(crate) fn record_sign_constraint(
        &mut self,
        subject: TermId,
        constraint: SignConstraint,
        assertion: TermId,
    ) {
        nonlinear::record_sign_constraint(
            self.terms,
            &self.aux_to_monomial,
            &mut self.sign_constraints,
            &mut self.var_sign_constraints,
            subject,
            constraint,
            assertion,
        );
    }
}

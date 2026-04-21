// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tangent plane constraints and nonlinear term collection for `NiaSolver`.
//!
//! Adds tangent plane linear cuts to the LIA solver when monomial values
//! disagree with factor products, and collects nonlinear subterms from
//! assertion terms.
//!
//! The standalone tangent plane math helpers live in `tangent_lemmas.rs`.
//! Extracted from `lib.rs` to keep each file under 500 lines.

use super::*;

impl NiaSolver<'_> {
    /// Add a tangent plane constraint to cut off an incorrect model point
    ///
    /// For monomial m = x*y at model point (a, b):
    /// - Correct value: c = a * b
    /// - Current value: v = val(m)
    /// - Tangent plane: T(x,y) = a*y + b*x - a*b
    ///
    /// If v < c (below surface): add m >= T, i.e., m - a*y - b*x >= -a*b
    /// If v > c (above surface): add m <= T, i.e., m - a*y - b*x <= -a*b
    ///
    /// Returns true if a constraint was added.
    #[allow(clippy::many_single_char_names)]
    pub(crate) fn add_tangent_constraint(
        &mut self,
        mon: &Monomial,
        a: &BigRational,
        b: &BigRational,
        is_below: bool,
    ) -> bool {
        // Only handle binary monomials for now
        if !mon.is_binary() {
            return false;
        }

        let Some(x) = mon.x() else { return false };
        let Some(y) = mon.y() else { return false };
        let m = mon.aux_var;

        // Get LRA solver for adding the cut
        let lra = self.lia.lra_solver_mut();

        // Ensure all variables are registered with LRA
        let m_var = lra.ensure_var_registered(m);
        let x_var = lra.ensure_var_registered(x);
        let y_var = lra.ensure_var_registered(y);

        // Build the linear expression: m - a*y - b*x
        // Coefficients: (var_id, coefficient)
        let coeffs = vec![
            (m_var, BigRational::one()),
            (y_var, -a.clone()),
            (x_var, -b.clone()),
        ];

        // Bound value: -a*b
        let bound = -(a * b);

        // Create the cut
        let cut = GomoryCut {
            coeffs,
            bound,
            is_lower: is_below, // below -> m >= T (lower bound on expression)
            reasons: Vec::new(),
            source_term: None,
        };

        // Add the cut
        // Use m as the reason term (dummy for now - could track better)
        lra.add_gomory_cut(&cut, m);

        if self.debug {
            safe_eprintln!(
                "[NIA] Added tangent plane constraint at ({}, {}): {} for m={:?}, x={:?}, y={:?}",
                a,
                b,
                if is_below { ">=" } else { "<=" },
                m,
                x,
                y
            );
        }

        true
    }

    /// Check monomials and add tangent constraints for those with incorrect values.
    ///
    /// Returns the number of constraints added.
    #[allow(clippy::many_single_char_names)]
    pub(crate) fn add_tangent_constraints_for_incorrect_monomials(&mut self) -> usize {
        // Collect monomials that need tangent constraints
        let mut to_constrain: Vec<(Monomial, BigRational, BigRational, bool)> = Vec::new();

        // Sort monomials for deterministic constraint ordering (#3060)
        let mut sorted_mons: Vec<_> = self.monomials.values().collect();
        sorted_mons.sort_unstable_by(|a, b| a.vars.cmp(&b.vars));
        for mon in sorted_mons {
            if !mon.is_binary() {
                continue;
            }

            let Some(x) = mon.x() else { continue };
            let Some(y) = mon.y() else { continue };

            // Get factor values
            let Some(a) = self.var_value(x) else { continue };
            let Some(b) = self.var_value(y) else { continue };

            // Get monomial value
            let Some(v) = self.var_value(mon.aux_var) else {
                continue;
            };

            // Compute correct value
            let c = &a * &b;

            // Check if values match (exact equality for integers)
            if v == c {
                continue;
            }

            // Determine if we're below or above the surface
            let is_below = v < c;

            to_constrain.push((mon.clone(), a, b, is_below));
        }

        // Add the constraints
        let mut count = 0;
        for (mon, a, b, is_below) in to_constrain {
            if self.add_tangent_constraint(&mon, &a, &b, is_below) {
                count += 1;
            }
        }

        count
    }

    /// Recursively scan a term for nonlinear subterms and register them
    pub(crate) fn collect_nonlinear_terms(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "*" => {
                        // Find constant factors and variable factors
                        let mut var_args = Vec::new();
                        for &arg in args {
                            if self.terms.extract_integer_constant(arg).is_none() {
                                var_args.push(arg);
                            }
                        }

                        // If more than one variable factor, it's nonlinear
                        if var_args.len() >= 2 {
                            // Sort for canonical form
                            var_args.sort_by_key(|t| t.0);

                            // Register this monomial if not already registered
                            if !self.monomials.contains_key(&var_args) {
                                // The term itself serves as the auxiliary variable
                                // (representing the value of the product)
                                self.register_monomial(var_args.clone(), term);
                                if self.debug {
                                    safe_eprintln!(
                                        "[NIA] Registered nonlinear term {:?} with vars {:?}",
                                        term,
                                        var_args
                                    );
                                }
                            }
                        }

                        // Recurse into arguments
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                    "+" | "-" | "/" => {
                        // Recurse into arithmetic operations
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                    "<" | "<=" | ">" | ">=" | "=" | "distinct" => {
                        // Recurse into comparison operands
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                    _ => {
                        // Unknown function - still recurse
                        for &arg in args {
                            self.collect_nonlinear_terms(arg);
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                self.collect_nonlinear_terms(*inner);
            }
            TermData::Ite(cond, then_b, else_b) => {
                self.collect_nonlinear_terms(*cond);
                self.collect_nonlinear_terms(*then_b);
                self.collect_nonlinear_terms(*else_b);
            }
            TermData::Let(_, body) => {
                self.collect_nonlinear_terms(*body);
            }
            _ => {}
        }
    }

    /// Collect integer variables from a term
    pub(crate) fn collect_integer_vars(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::Var(_, _) => {
                if matches!(self.terms.sort(term), Sort::Int) {
                    self.lia.register_integer_var(term);
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.collect_integer_vars(arg);
                }
            }
            TermData::Not(inner) => {
                self.collect_integer_vars(*inner);
            }
            TermData::Ite(c, t, e) => {
                self.collect_integer_vars(*c);
                self.collect_integer_vars(*t);
                self.collect_integer_vars(*e);
            }
            TermData::Let(_, body) => {
                self.collect_integer_vars(*body);
            }
            _ => {}
        }
    }
}

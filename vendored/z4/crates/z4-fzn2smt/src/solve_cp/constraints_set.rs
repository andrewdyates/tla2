// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Set variable constraint translations for solve-cp.
//
// Boolean indicator encoding: var set of lo..hi → (hi-lo+1) bool vars.
// set_card = sum of indicators, set_intersect = elementwise AND,
// set_le = reversed lex on indicator arrays.

use anyhow::Result;
use z4_cp::propagator::Constraint;
use z4_cp::variable::IntVarId;
use z4_flatzinc_parser::ast::ConstraintItem;

use super::CpContext;

impl CpContext {
    /// set_card(S, c): |S| = c
    /// Encoding: sum of boolean indicators = c.
    pub(super) fn translate_set_card(&mut self, c: &ConstraintItem) -> Result<()> {
        let set_name = match &c.args[0] {
            z4_flatzinc_parser::ast::Expr::Ident(name) => name.clone(),
            _ => anyhow::bail!("set_card: expected set variable identifier"),
        };
        let (_, indicators) = self
            .set_var_map
            .get(&set_name)
            .ok_or_else(|| anyhow::anyhow!("set_card: unknown set variable: {set_name}"))?
            .clone();

        if let Some(card) = self.eval_const_int(&c.args[1]) {
            let n = indicators.len();
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs: vec![1; n],
                vars: indicators,
                rhs: card,
            });
        } else {
            let c_var = self.resolve_var(&c.args[1])?;
            let n = indicators.len();
            let mut coeffs = vec![1i64; n];
            coeffs.push(-1);
            let mut vars = indicators;
            vars.push(c_var);
            self.engine.add_constraint(Constraint::LinearEq {
                coeffs,
                vars,
                rhs: 0,
            });
        }
        Ok(())
    }

    /// set_intersect(S1, S2, S3): S3 = S1 ∩ S2
    /// Encoding: for each position i, b3[i] = b1[i] AND b2[i].
    pub(super) fn translate_set_intersect(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_intersect")?;
        let name2 = resolve_set_name(&c.args[1], "set_intersect")?;
        let name3 = resolve_set_name(&c.args[2], "set_intersect")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;
        let (lo3, ind3) = self.get_set_indicators(&name3)?;

        let hi1 = lo1 + ind1.len() as i64 - 1;
        let hi2 = lo2 + ind2.len() as i64 - 1;
        let hi3 = lo3 + ind3.len() as i64 - 1;
        let lo = lo1.min(lo2).min(lo3);
        let hi = hi1.max(hi2).max(hi3);

        for elem in lo..=hi {
            let b1 = get_indicator(&ind1, lo1, elem);
            let b2 = get_indicator(&ind2, lo2, elem);
            let b3 = get_indicator(&ind3, lo3, elem);

            match (b1, b2, b3) {
                (Some(i1), Some(i2), Some(i3)) => {
                    // i3 = i1 AND i2
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, -1],
                        vars: vec![i3, i1],
                        rhs: 0,
                    });
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, -1],
                        vars: vec![i3, i2],
                        rhs: 0,
                    });
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, 1, -1],
                        vars: vec![i1, i2, i3],
                        rhs: 1,
                    });
                }
                (_, _, Some(i3)) => {
                    self.engine.add_constraint(Constraint::LinearEq {
                        coeffs: vec![1],
                        vars: vec![i3],
                        rhs: 0,
                    });
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// set_union(S1, S2, S3): S3 = S1 ∪ S2
    /// Encoding: for each position i, b3[i] = b1[i] OR b2[i].
    pub(super) fn translate_set_union(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_union")?;
        let name2 = resolve_set_name(&c.args[1], "set_union")?;
        let name3 = resolve_set_name(&c.args[2], "set_union")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;
        let (lo3, ind3) = self.get_set_indicators(&name3)?;

        let hi1 = lo1 + ind1.len() as i64 - 1;
        let hi2 = lo2 + ind2.len() as i64 - 1;
        let hi3 = lo3 + ind3.len() as i64 - 1;
        let lo = lo1.min(lo2).min(lo3);
        let hi = hi1.max(hi2).max(hi3);

        for elem in lo..=hi {
            let b1 = get_indicator(&ind1, lo1, elem);
            let b2 = get_indicator(&ind2, lo2, elem);
            let b3 = get_indicator(&ind3, lo3, elem);

            match (b1, b2, b3) {
                (Some(i1), Some(i2), Some(i3)) => {
                    // i3 = i1 OR i2: i3 >= i1, i3 >= i2, i3 <= i1 + i2
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, -1],
                        vars: vec![i1, i3],
                        rhs: 0,
                    });
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, -1],
                        vars: vec![i2, i3],
                        rhs: 0,
                    });
                    self.engine.add_constraint(Constraint::LinearLe {
                        coeffs: vec![1, -1, -1],
                        vars: vec![i3, i1, i2],
                        rhs: 0,
                    });
                }
                (Some(i1), None, Some(i3)) => {
                    // OR with absent element = identity
                    self.engine.add_constraint(Constraint::LinearEq {
                        coeffs: vec![1, -1],
                        vars: vec![i3, i1],
                        rhs: 0,
                    });
                }
                (None, Some(i2), Some(i3)) => {
                    self.engine.add_constraint(Constraint::LinearEq {
                        coeffs: vec![1, -1],
                        vars: vec![i3, i2],
                        rhs: 0,
                    });
                }
                (None, None, Some(i3)) => {
                    // Neither set can contain elem
                    self.engine.add_constraint(Constraint::LinearEq {
                        coeffs: vec![1],
                        vars: vec![i3],
                        rhs: 0,
                    });
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// array_set_element(i, array_of_sets, S): S = array_of_sets[i]
    ///
    /// Two cases:
    /// - Constant array of sets (Ident → par_set_arrays): build constant indicator
    ///   tables and use Element per indicator position.
    /// - Variable array of sets (ArrayLit of set var Idents): link set variable
    ///   indicators via Element per indicator position.
    pub(super) fn translate_array_set_element(&mut self, c: &ConstraintItem) -> Result<()> {
        use z4_flatzinc_parser::ast::Expr;

        let index = self.resolve_var(&c.args[0])?;
        let result_name = resolve_set_name(&c.args[2], "array_set_element")?;
        let (res_lo, res_ind) = self.get_set_indicators(&result_name)?;
        let res_hi = res_lo + res_ind.len() as i64 - 1;

        match &c.args[1] {
            Expr::Ident(name) => {
                // Constant parameter array of sets.
                let const_sets = self.par_set_arrays.get(name).cloned().ok_or_else(|| {
                    anyhow::anyhow!("array_set_element: unknown parameter set array: {name}")
                })?;
                if const_sets.is_empty() {
                    return Ok(());
                }
                let n = const_sets.len() as i64;
                let index_0 = self.engine.new_int_var(z4_cp::Domain::new(0, n - 1), None);
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![index, index_0],
                    rhs: 1,
                });
                // For each value v in the result set's range, build a constant
                // membership table and add an Element constraint.
                for v in res_lo..=res_hi {
                    let Some(res_v) = get_indicator(&res_ind, res_lo, v) else {
                        continue;
                    };
                    let table: Vec<IntVarId> = const_sets
                        .iter()
                        .map(|s| {
                            let member = if s.contains(&v) { 1 } else { 0 };
                            self.get_const_var(member)
                        })
                        .collect();
                    self.engine.add_constraint(Constraint::Element {
                        index: index_0,
                        array: table,
                        result: res_v,
                    });
                }
            }
            Expr::ArrayLit(elems) => {
                // Variable array of sets.
                let set_names: Vec<String> = elems
                    .iter()
                    .map(|e| resolve_set_name(e, "array_set_element"))
                    .collect::<Result<Vec<_>>>()?;
                if set_names.is_empty() {
                    return Ok(());
                }
                let mut array_sets: Vec<(i64, Vec<IntVarId>)> = Vec::new();
                let mut lo = res_lo;
                let mut hi = res_hi;
                for name in &set_names {
                    let (s_lo, s_ind) = self.get_set_indicators(name)?;
                    let s_hi = s_lo + s_ind.len() as i64 - 1;
                    lo = lo.min(s_lo);
                    hi = hi.max(s_hi);
                    array_sets.push((s_lo, s_ind));
                }
                let n = array_sets.len() as i64;
                let zero = self.get_const_var(0);
                let index_0 = self.engine.new_int_var(z4_cp::Domain::new(0, n - 1), None);
                self.engine.add_constraint(Constraint::LinearEq {
                    coeffs: vec![1, -1],
                    vars: vec![index, index_0],
                    rhs: 1,
                });
                for v in lo..=hi {
                    let Some(res_v) = get_indicator(&res_ind, res_lo, v) else {
                        continue;
                    };
                    let elem_inds: Vec<IntVarId> = array_sets
                        .iter()
                        .map(|(s_lo, s_ind)| get_indicator(s_ind, *s_lo, v).unwrap_or(zero))
                        .collect();
                    self.engine.add_constraint(Constraint::Element {
                        index: index_0,
                        array: elem_inds,
                        result: res_v,
                    });
                }
            }
            _ => {
                anyhow::bail!("array_set_element: expected identifier or array literal");
            }
        }
        Ok(())
    }

    /// set_le(S1, S2): S1 ≤ S2 in standard set ordering.
    /// Standard set ordering = lex on sorted element sequences.
    /// With boolean indicators, this is lex_ge on indicator arrays
    /// (because indicator lex is the reverse of element lex).
    pub(super) fn translate_set_le(&mut self, c: &ConstraintItem) -> Result<()> {
        let name1 = resolve_set_name(&c.args[0], "set_le")?;
        let name2 = resolve_set_name(&c.args[1], "set_le")?;

        let (lo1, ind1) = self.get_set_indicators(&name1)?;
        let (lo2, ind2) = self.get_set_indicators(&name2)?;

        let hi1 = lo1 + ind1.len() as i64 - 1;
        let hi2 = lo2 + ind2.len() as i64 - 1;
        let lo = lo1.min(lo2);
        let hi = hi1.max(hi2);

        let zero = self.get_const_var(0);
        let mut xs = Vec::new();
        let mut ys = Vec::new();

        for elem in lo..=hi {
            xs.push(get_indicator(&ind2, lo2, elem).unwrap_or(zero));
            ys.push(get_indicator(&ind1, lo1, elem).unwrap_or(zero));
        }

        // set_le(S1, S2) = lex_lesseq(ind(S2), ind(S1))
        self.add_lex_lesseq_vars(&xs, &ys);
        Ok(())
    }

    /// Helper: lex_lesseq on pre-resolved variable arrays (typically boolean
    /// set indicators). Uses full bidirectional reification for chain equality
    /// indicators to prevent the solver from under-counting equal positions.
    ///
    /// The encoding follows the same pattern as `translate_lex_lesseq_int`:
    ///   prev_b ↔ (xs[0] == ys[0]) ∧ ... ∧ (xs[i-1] == ys[i-1])
    ///   prev_b=1 → xs[i] <= ys[i]
    pub(super) fn add_lex_lesseq_vars(&mut self, xs: &[IntVarId], ys: &[IntVarId]) {
        let n = xs.len().min(ys.len());
        if n == 0 {
            return;
        }
        // xs[0] <= ys[0] (unconditional)
        self.engine.add_constraint(Constraint::LinearLe {
            coeffs: vec![1, -1],
            vars: vec![xs[0], ys[0]],
            rhs: 0,
        });
        if n == 1 {
            return;
        }

        // b_0 ↔ (xs[0] == ys[0]) — full bidirectional reification
        let mut prev_b = self.engine.new_bool_var(None);
        self.var_bounds.insert(prev_b, (0, 1));
        self.add_reif_eq(&[1, -1], &[xs[0], ys[0]], 0, prev_b);

        for i in 1..n {
            let m = {
                let (a_lb, a_ub) = self.get_var_bounds(xs[i]);
                let (b_lb, b_ub) = self.get_var_bounds(ys[i]);
                (a_ub - b_lb).max(b_ub - a_lb).max(1)
            };

            // If prefix was all-equal (prev_b=1), then xs[i] <= ys[i]
            // xs[i] - ys[i] <= M*(1-prev_b)
            self.engine.add_constraint(Constraint::LinearLe {
                coeffs: vec![1, -1, m],
                vars: vec![xs[i], ys[i], prev_b],
                rhs: m,
            });

            if i < n - 1 {
                // eq_i ↔ (xs[i] == ys[i]) — full reification
                let eq_i = self.engine.new_bool_var(None);
                self.var_bounds.insert(eq_i, (0, 1));
                self.add_reif_eq(&[1, -1], &[xs[i], ys[i]], 0, eq_i);

                // new_b ↔ (prev_b ∧ eq_i)
                let new_b = self.engine.new_bool_var(None);
                self.var_bounds.insert(new_b, (0, 1));
                // new_b ≤ prev_b
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![new_b, prev_b],
                    rhs: 0,
                });
                // new_b ≤ eq_i
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, -1],
                    vars: vec![new_b, eq_i],
                    rhs: 0,
                });
                // prev_b + eq_i - new_b ≤ 1 (forces new_b=1 when both are 1)
                self.engine.add_constraint(Constraint::LinearLe {
                    coeffs: vec![1, 1, -1],
                    vars: vec![prev_b, eq_i, new_b],
                    rhs: 1,
                });
                prev_b = new_b;
            }
        }
    }

    /// Look up a set variable's indicators, returning (lo, indicators).
    fn get_set_indicators(&self, name: &str) -> Result<(i64, Vec<IntVarId>)> {
        self.set_var_map
            .get(name)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("unknown set variable: {name}"))
    }
}

fn resolve_set_name(expr: &z4_flatzinc_parser::ast::Expr, constraint: &str) -> Result<String> {
    match expr {
        z4_flatzinc_parser::ast::Expr::Ident(n) => Ok(n.clone()),
        _ => anyhow::bail!("{constraint}: expected set variable identifier"),
    }
}

fn get_indicator(indicators: &[IntVarId], lo: i64, elem: i64) -> Option<IntVarId> {
    let idx = (elem - lo) as usize;
    indicators.get(idx).copied()
}

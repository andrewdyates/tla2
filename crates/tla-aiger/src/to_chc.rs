// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// AIGER to CHC translation: converts parsed AIGER circuits into z4-chc's
// `ChcProblem` format for the PDR/BMC portfolio solver.
//
// Translation scheme for safety checking:
//   latch      -> Bool ChcVar in the invariant predicate
//   input      -> existentially quantified Bool variable in transition clause
//   AND gate   -> Boolean conjunction of (possibly negated) operands
//   init       -> init clause: all latches = reset value => Inv(latches)
//   next       -> transition clause: Inv(curr) /\ trans => Inv(next)
//   bad        -> query clause: Inv(curr) /\ bad_expr => false
//   constraint -> conjoined with transition relation

use std::time::Duration;

use rustc_hash::FxHashMap;
use z4_chc::{
    AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, HornClause, VerifiedChcResult,
};

use crate::error::AigerError;
use crate::types::*;

// ---------------------------------------------------------------------------
// Public result types
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub struct AigerTranslation {
    pub problem: ChcProblem,
    pub latch_vars: Vec<LatchVarEntry>,
    pub property_indices: Vec<usize>,
}

#[derive(Debug, Clone)]
pub struct LatchVarEntry {
    pub latch_idx: usize,
    pub name: Option<String>,
    pub curr_var: ChcVar,
    pub next_var: ChcVar,
}

#[derive(Debug)]
pub enum AigerCheckResult {
    Sat { trace: Vec<FxHashMap<String, i64>> },
    Unsat,
    Unknown { reason: String },
}

// ---------------------------------------------------------------------------
// Translator
// ---------------------------------------------------------------------------

struct Translator<'a> {
    circuit: &'a AigerCircuit,
    expr_cache: FxHashMap<u64, ChcExpr>,
    and_index: FxHashMap<u64, usize>,
    input_vars: FxHashMap<u64, ChcVar>,
    latch_curr: FxHashMap<u64, ChcVar>,
    latch_entries: Vec<LatchVarEntry>,
}

impl<'a> Translator<'a> {
    fn new(circuit: &'a AigerCircuit) -> Self {
        let mut and_index = FxHashMap::default();
        for (idx, gate) in circuit.ands.iter().enumerate() {
            and_index.insert(aiger_var(gate.lhs), idx);
        }

        Self {
            circuit,
            expr_cache: FxHashMap::default(),
            and_index,
            input_vars: FxHashMap::default(),
            latch_curr: FxHashMap::default(),
            latch_entries: Vec::new(),
        }
    }

    fn create_variables(&mut self) {
        for (idx, latch) in self.circuit.latches.iter().enumerate() {
            let var_idx = aiger_var(latch.lit);
            let name = latch.name.clone().unwrap_or_else(|| format!("l{idx}"));

            let curr_var = ChcVar {
                name: name.clone(),
                sort: ChcSort::Bool,
            };
            let next_var = ChcVar {
                name: format!("{name}'"),
                sort: ChcSort::Bool,
            };

            self.latch_curr.insert(var_idx, curr_var.clone());
            self.latch_entries.push(LatchVarEntry {
                latch_idx: idx,
                name: latch.name.clone(),
                curr_var,
                next_var,
            });
        }

        for (idx, input) in self.circuit.inputs.iter().enumerate() {
            let var_idx = aiger_var(input.lit);
            let name = input.name.clone().unwrap_or_else(|| format!("i{idx}"));
            self.input_vars.insert(
                var_idx,
                ChcVar {
                    name,
                    sort: ChcSort::Bool,
                },
            );
        }
    }

    fn translate_lit(&mut self, lit: Literal) -> Result<ChcExpr, AigerError> {
        if lit == 0 {
            return Ok(ChcExpr::Bool(false));
        }
        if lit == 1 {
            return Ok(ChcExpr::Bool(true));
        }

        let var_idx = aiger_var(lit);
        let negated = aiger_is_negated(lit);

        let base_expr = if let Some(cached) = self.expr_cache.get(&var_idx) {
            cached.clone()
        } else {
            let expr = self.translate_var(var_idx)?;
            self.expr_cache.insert(var_idx, expr.clone());
            expr
        };

        if negated {
            Ok(ChcExpr::not(base_expr))
        } else {
            Ok(base_expr)
        }
    }

    fn translate_var(&mut self, var_idx: u64) -> Result<ChcExpr, AigerError> {
        if let Some(var) = self.input_vars.get(&var_idx) {
            return Ok(ChcExpr::var(var.clone()));
        }
        if let Some(var) = self.latch_curr.get(&var_idx) {
            return Ok(ChcExpr::var(var.clone()));
        }
        if let Some(&gate_idx) = self.and_index.get(&var_idx) {
            let gate = self.circuit.ands[gate_idx].clone();
            let rhs0 = self.translate_lit(gate.rhs0)?;
            let rhs1 = self.translate_lit(gate.rhs1)?;
            return Ok(ChcExpr::and(rhs0, rhs1));
        }

        Err(AigerError::UndefinedLiteral(var_idx * 2))
    }

    fn assemble(mut self) -> Result<AigerTranslation, AigerError> {
        self.create_variables();

        let mut problem = ChcProblem::new();

        // Declare the invariant predicate over latch sorts
        let inv_sorts: Vec<ChcSort> = self.latch_entries.iter().map(|_| ChcSort::Bool).collect();
        let inv_pred = problem.declare_predicate("Inv", inv_sorts);

        let curr_args: Vec<ChcExpr> = self
            .latch_entries
            .iter()
            .map(|e| ChcExpr::var(e.curr_var.clone()))
            .collect();
        let next_args: Vec<ChcExpr> = self
            .latch_entries
            .iter()
            .map(|e| ChcExpr::var(e.next_var.clone()))
            .collect();

        // Init clause: init_constraint => Inv(latches)
        // Collect init work items first to avoid borrow conflict with translate_lit.
        let init_work: Vec<(ChcVar, Literal, Literal)> = self
            .latch_entries
            .iter()
            .map(|entry| {
                let latch = &self.circuit.latches[entry.latch_idx];
                (entry.curr_var.clone(), latch.reset, latch.lit)
            })
            .collect();

        let mut init_conjuncts = Vec::new();
        for (curr_var, reset, latch_lit) in init_work {
            if reset == latch_lit {
                continue; // Nondeterministic reset
            }
            let curr_expr = ChcExpr::var(curr_var);
            let reset_val = if reset == 0 {
                ChcExpr::Bool(false)
            } else if reset == 1 {
                ChcExpr::Bool(true)
            } else {
                self.translate_lit(reset)?
            };
            init_conjuncts.push(ChcExpr::eq(curr_expr, reset_val));
        }

        let init_constraint = if init_conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(init_conjuncts)
        };

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(init_constraint),
            ClauseHead::Predicate(inv_pred, curr_args.clone()),
        ));

        // Transition clause: Inv(curr) /\ trans => Inv(next)
        let mut trans_conjuncts = Vec::new();

        let entries_clone: Vec<_> = self.latch_entries.clone();
        for entry in &entries_clone {
            let latch = &self.circuit.latches[entry.latch_idx];
            let next_expr = self.translate_lit(latch.next)?;
            trans_conjuncts.push(ChcExpr::eq(ChcExpr::var(entry.next_var.clone()), next_expr));
        }

        // Add environment constraints
        let constraint_lits: Vec<Literal> =
            self.circuit.constraints.iter().map(|c| c.lit).collect();
        for lit in constraint_lits {
            let expr = self.translate_lit(lit)?;
            trans_conjuncts.push(expr);
        }

        let trans_constraint = if trans_conjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(trans_conjuncts))
        };

        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv_pred, curr_args.clone())], trans_constraint),
            ClauseHead::Predicate(inv_pred, next_args),
        ));

        // Query clauses: Inv(curr) /\ bad => false
        // Use bad properties if present, else outputs (legacy convention)
        let property_lits: Vec<Literal> = if !self.circuit.bad.is_empty() {
            self.circuit.bad.iter().map(|b| b.lit).collect()
        } else {
            self.circuit.outputs.iter().map(|o| o.lit).collect()
        };

        let mut property_indices = Vec::with_capacity(property_lits.len());
        for lit in property_lits {
            let clause_idx = problem.clauses().len();
            property_indices.push(clause_idx);
            let bad_expr = self.translate_lit(lit)?;
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![(inv_pred, curr_args.clone())], Some(bad_expr)),
                ClauseHead::False,
            ));
        }

        Ok(AigerTranslation {
            problem,
            latch_vars: self.latch_entries,
            property_indices,
        })
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Translate an AIGER circuit to a CHC problem for safety checking.
pub fn translate_to_chc(circuit: &AigerCircuit) -> Result<AigerTranslation, AigerError> {
    Translator::new(circuit).assemble()
}

/// Check all safety properties of an AIGER circuit using z4-chc.
pub fn check_aiger(
    circuit: &AigerCircuit,
    time_budget: Option<Duration>,
) -> Result<Vec<AigerCheckResult>, AigerError> {
    let properties: Vec<Literal> = if !circuit.bad.is_empty() {
        circuit.bad.iter().map(|b| b.lit).collect()
    } else {
        circuit.outputs.iter().map(|o| o.lit).collect()
    };

    if properties.is_empty() {
        return Ok(vec![]);
    }

    let translation = translate_to_chc(circuit)?;
    let config = match time_budget {
        Some(budget) => AdaptiveConfig::with_budget(budget, false),
        None => AdaptiveConfig::default(),
    };
    let portfolio = AdaptivePortfolio::new(translation.problem, config);
    let result = portfolio.solve();

    let n = properties.len();
    match result {
        VerifiedChcResult::Safe(_) => Ok((0..n).map(|_| AigerCheckResult::Unsat).collect()),
        VerifiedChcResult::Unsafe(cex) => {
            let trace: Vec<FxHashMap<String, i64>> = cex
                .counterexample()
                .steps
                .iter()
                .map(|step| step.assignments.clone())
                .collect();

            let violated_prop = cex
                .counterexample()
                .witness
                .as_ref()
                .and_then(|w| w.query_clause)
                .and_then(|clause_idx| {
                    translation
                        .property_indices
                        .iter()
                        .position(|&pi| pi == clause_idx)
                });

            let mut results = Vec::with_capacity(n);
            if let Some(prop_idx) = violated_prop {
                for i in 0..n {
                    if i == prop_idx {
                        results.push(AigerCheckResult::Sat {
                            trace: trace.clone(),
                        });
                    } else {
                        results.push(AigerCheckResult::Unknown {
                            reason: "other property violated".to_string(),
                        });
                    }
                }
            } else if n == 1 {
                results.push(AigerCheckResult::Sat { trace });
            } else {
                for _ in 0..n {
                    results.push(AigerCheckResult::Unknown {
                        reason: "counterexample found but violated property unknown".to_string(),
                    });
                }
            }
            Ok(results)
        }
        VerifiedChcResult::Unknown(reason) => Ok((0..n)
            .map(|_| AigerCheckResult::Unknown {
                reason: reason.to_string(),
            })
            .collect()),
        _ => Ok((0..n)
            .map(|_| AigerCheckResult::Unknown {
                reason: "unexpected solver result".to_string(),
            })
            .collect()),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;

    #[test]
    fn test_translate_trivially_safe() {
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let translation = translate_to_chc(&circuit).unwrap();
        assert_eq!(translation.property_indices.len(), 1);
    }

    #[test]
    fn test_translate_trivially_unsafe() {
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let translation = translate_to_chc(&circuit).unwrap();
        assert_eq!(translation.property_indices.len(), 1);
    }

    #[test]
    fn test_translate_with_latch() {
        let circuit = parse_aag("aag 1 0 1 1 0\n2 3\n2\n").unwrap();
        let translation = translate_to_chc(&circuit).unwrap();
        assert_eq!(translation.latch_vars.len(), 1);
        assert_eq!(translation.property_indices.len(), 1);
    }

    #[test]
    fn test_translate_and_gate() {
        // M=3 I=2 L=0 O=0 A=1 B=1: inputs 2,4; AND gate 6=2&4; bad=6
        let src = "aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n";
        let circuit = parse_aag(src).unwrap();
        let translation = translate_to_chc(&circuit).unwrap();
        assert_eq!(translation.property_indices.len(), 1);
    }

    #[test]
    fn test_check_toggle_reachable() {
        // Toggle flip-flop: latch starts at 0, toggles to 1 on step 1.
        // Bad = latch (lit 2). Reachable at step 1 => SAT.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let results = check_aiger(&circuit, Some(Duration::from_secs(10))).unwrap();
        assert_eq!(results.len(), 1);
        assert!(matches!(results[0], AigerCheckResult::Sat { .. }));
    }

    #[test]
    fn test_check_latch_stays_zero() {
        // Latch with next=0 (stuck at 0). Bad = latch (lit 2).
        // Latch is always 0 => bad is never true => UNSAT.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let results = check_aiger(&circuit, Some(Duration::from_secs(10))).unwrap();
        assert_eq!(results.len(), 1);
        assert!(matches!(results[0], AigerCheckResult::Unsat));
    }

    #[test]
    fn test_no_properties() {
        let circuit = parse_aag("aag 1 1 0 0 0\n2\n").unwrap();
        let results = check_aiger(&circuit, Some(Duration::from_secs(5))).unwrap();
        assert!(results.is_empty());
    }
}

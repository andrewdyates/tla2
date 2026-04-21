// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::LiveExpr;

impl LiveExpr {
    /// Maximum number of DNF clauses before aborting with an error.
    ///
    /// The DNF computation is exponential in the number of fairness constraints
    /// (each WF/SF with 2 branches doubles the clause count). With N fairness
    /// constraints, the DNF has up to 2^N clauses. This limit prevents runaway
    /// computation. TLC avoids this by checking fairness as SCC acceptability
    /// conditions rather than encoding them in the DNF formula.
    pub(crate) const MAX_DNF_CLAUSES: usize = 500_000;

    /// Convert this formula to disjunctive normal form (DNF).
    ///
    /// This treats temporal operators ([], <>, ()) as atomic for the purpose of DNF;
    /// it only distributes over explicit boolean connectives (/\ and \/).
    ///
    /// The returned value is a disjunction of conjunction clauses:
    /// - outer `Vec`: disjuncts
    /// - inner `Vec`: conjuncts within a disjunct
    ///
    /// Returns `Err(estimated_clause_count)` when expansion exceeds the clause
    /// limit to prevent exponential blow-up.
    pub fn to_dnf_clauses(&self) -> Result<Vec<Vec<LiveExpr>>, usize> {
        self.to_dnf_clauses_limited()
    }

    fn to_dnf_clauses_limited(&self) -> Result<Vec<Vec<LiveExpr>>, usize> {
        match self {
            LiveExpr::Bool(true) => Ok(vec![vec![]]),
            LiveExpr::Bool(false) => Ok(vec![]),
            LiveExpr::And(conjuncts) => {
                let mut clauses: Vec<Vec<LiveExpr>> = vec![vec![]];
                for conjunct in conjuncts {
                    let conjunct_clauses = conjunct.to_dnf_clauses_limited()?;
                    if conjunct_clauses.is_empty() {
                        return Ok(vec![]);
                    }

                    let new_count = clauses.len().saturating_mul(conjunct_clauses.len());
                    if new_count > Self::MAX_DNF_CLAUSES {
                        return Err(new_count);
                    }

                    let mut next_clauses = Vec::with_capacity(new_count);
                    for base in &clauses {
                        for add in &conjunct_clauses {
                            let mut merged = base.clone();
                            merged.extend(add.iter().cloned());
                            next_clauses.push(merged);
                        }
                    }
                    clauses = next_clauses;
                }
                Ok(clauses)
            }
            LiveExpr::Or(disjuncts) => {
                let mut clauses = Vec::new();
                for disjunct in disjuncts {
                    clauses.extend(disjunct.to_dnf_clauses_limited()?);
                    if clauses.len() > Self::MAX_DNF_CLAUSES {
                        return Err(clauses.len());
                    }
                }
                Ok(clauses)
            }
            _ => Ok(vec![vec![self.clone()]]),
        }
    }
}

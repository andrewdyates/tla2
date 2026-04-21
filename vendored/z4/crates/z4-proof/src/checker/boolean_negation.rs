// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negation-decomposition and contraction Alethe proof rules.
//!
//! Contains `not_and`, `not_or`, `not_implies`, `not_equiv`, `not_ite`,
//! and `contraction` validators. Extracted from `boolean_derived.rs`
//! for code health (#5970).

use z4_core::{ProofId, TermId, TermStore};

use super::boolean::{
    clause_matches_expected, clause_matches_unordered, decode_app, decode_ite, err, make_err,
    strip_not, ExpectedLit,
};
use super::ProofCheckError;

pub(crate) fn validate_not_and(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_and", "rule requires exactly one unit premise");
    }
    let and_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_and", "premise must be (not (and ...))"))?;
    let args = decode_app(terms, and_term, "and")
        .ok_or_else(|| make_err(step, "not_and", "premise must negate an and term"))?;
    let expected: Vec<ExpectedLit> = args.iter().map(|&arg| ExpectedLit::Not(arg)).collect();
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "not_and",
            "clause must contain negations of all conjuncts",
        );
    }
    Ok(())
}

pub(crate) fn validate_not_or(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 || clause.len() != 1 {
        return err(
            step,
            "not_or",
            "rule requires one unit premise and one conclusion literal",
        );
    }
    let or_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_or", "premise must be (not (or ...))"))?;
    let args = decode_app(terms, or_term, "or")
        .ok_or_else(|| make_err(step, "not_or", "premise must negate an or term"))?;
    let negated = strip_not(terms, clause[0])
        .ok_or_else(|| make_err(step, "not_or", "conclusion must be a negation"))?;
    if !args.contains(&negated) {
        return err(step, "not_or", "conclusion must negate a premise disjunct");
    }
    Ok(())
}

pub(crate) fn validate_not_implies1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 || clause.len() != 1 {
        return err(
            step,
            "not_implies1",
            "rule requires one unit premise and one conclusion literal",
        );
    }
    let imp_term = strip_not(terms, premise_clauses[0][0]).ok_or_else(|| {
        make_err(
            step,
            "not_implies1",
            "premise must be a negated implication",
        )
    })?;
    if let Some(args) = decode_app(terms, imp_term, "=>") {
        if args.len() != 2 || clause[0] != args[0] {
            return err(step, "not_implies1", "conclusion must be F1");
        }
        return Ok(());
    }
    if let Some(args) = decode_app(terms, imp_term, "or") {
        if args.len() != 2 {
            return err(step, "not_implies1", "desugared implication must be binary");
        }
        let f1 = strip_not(terms, args[0]).ok_or_else(|| {
            make_err(
                step,
                "not_implies1",
                "desugared implication must start with (not F1)",
            )
        })?;
        if clause[0] != f1 {
            return err(step, "not_implies1", "conclusion must be F1");
        }
        return Ok(());
    }
    err(step, "not_implies1", "premise must negate an implication")
}

pub(crate) fn validate_not_implies2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 || clause.len() != 1 {
        return err(
            step,
            "not_implies2",
            "rule requires one unit premise and one conclusion literal",
        );
    }
    let imp_term = strip_not(terms, premise_clauses[0][0]).ok_or_else(|| {
        make_err(
            step,
            "not_implies2",
            "premise must be a negated implication",
        )
    })?;
    let expected = if let Some(args) = decode_app(terms, imp_term, "=>") {
        if args.len() != 2 {
            return err(step, "not_implies2", "implication must be binary");
        }
        clause[0]
    } else if let Some(args) = decode_app(terms, imp_term, "or") {
        if args.len() != 2 {
            return err(step, "not_implies2", "desugared implication must be binary");
        }
        clause[0]
    } else {
        return err(step, "not_implies2", "premise must negate an implication");
    };
    if strip_not(terms, expected) != Some(args_from_not_implies2(terms, imp_term, step)?) {
        return err(step, "not_implies2", "conclusion must be (not F2)");
    }
    Ok(())
}

pub(crate) fn validate_not_equiv1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_equiv1", "rule requires exactly one unit premise");
    }
    let eq_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_equiv1", "premise must be (not (= ...))"))?;
    let args = decode_app(terms, eq_term, "=")
        .ok_or_else(|| make_err(step, "not_equiv1", "premise must negate an equality"))?;
    if args.len() != 2 || !clause_matches_unordered(clause, args) {
        return err(
            step,
            "not_equiv1",
            "conclusion must contain both equality sides",
        );
    }
    Ok(())
}

pub(crate) fn validate_not_equiv2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_equiv2", "rule requires exactly one unit premise");
    }
    let eq_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_equiv2", "premise must be (not (= ...))"))?;
    let args = decode_app(terms, eq_term, "=")
        .ok_or_else(|| make_err(step, "not_equiv2", "premise must negate an equality"))?;
    if args.len() != 2 {
        return err(step, "not_equiv2", "equality must be binary");
    }
    let expected = [ExpectedLit::Not(args[0]), ExpectedLit::Not(args[1])];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "not_equiv2",
            "conclusion must negate both equality sides",
        );
    }
    Ok(())
}

pub(crate) fn validate_not_ite1(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_ite1", "rule requires exactly one unit premise");
    }
    let ite_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_ite1", "premise must be (not (ite ...))"))?;
    let (c, _t, e) = decode_ite(terms, ite_term)
        .ok_or_else(|| make_err(step, "not_ite1", "premise must negate an ite term"))?;
    let expected = [ExpectedLit::Lit(c), ExpectedLit::Not(e)];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(step, "not_ite1", "conclusion must contain F1 and (not F3)");
    }
    Ok(())
}

pub(crate) fn validate_not_ite2(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 || premise_clauses[0].len() != 1 {
        return err(step, "not_ite2", "rule requires exactly one unit premise");
    }
    let ite_term = strip_not(terms, premise_clauses[0][0])
        .ok_or_else(|| make_err(step, "not_ite2", "premise must be (not (ite ...))"))?;
    let (c, t, _e) = decode_ite(terms, ite_term)
        .ok_or_else(|| make_err(step, "not_ite2", "premise must negate an ite term"))?;
    let expected = [ExpectedLit::Not(c), ExpectedLit::Not(t)];
    if !clause_matches_expected(terms, clause, &expected) {
        return err(
            step,
            "not_ite2",
            "conclusion must contain (not F1) and (not F2)",
        );
    }
    Ok(())
}

fn args_from_not_implies2(
    terms: &TermStore,
    imp_term: TermId,
    step: ProofId,
) -> Result<TermId, ProofCheckError> {
    if let Some(args) = decode_app(terms, imp_term, "=>") {
        if args.len() != 2 {
            return Err(make_err(step, "not_implies2", "implication must be binary"));
        }
        return Ok(args[1]);
    }
    if let Some(args) = decode_app(terms, imp_term, "or") {
        if args.len() != 2 {
            return Err(make_err(
                step,
                "not_implies2",
                "desugared implication must be binary",
            ));
        }
        return Ok(args[1]);
    }
    Err(make_err(
        step,
        "not_implies2",
        "premise must negate an implication",
    ))
}

pub(crate) fn validate_contraction(
    _terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_clauses: &[&[TermId]],
) -> Result<(), ProofCheckError> {
    if premise_clauses.len() != 1 {
        return err(step, "contraction", "must have exactly 1 premise");
    }
    let premise = premise_clauses[0];
    for &lit in clause {
        if !premise.contains(&lit) {
            return err(
                step,
                "contraction",
                "result literal not found in premise clause",
            );
        }
    }
    for (idx, &lit) in clause.iter().enumerate() {
        if clause[idx + 1..].contains(&lit) {
            return err(step, "contraction", "result clause has duplicate literals");
        }
    }
    for &lit in premise {
        if !clause.contains(&lit) {
            return err(
                step,
                "contraction",
                "premise literal missing from result clause",
            );
        }
    }
    Ok(())
}

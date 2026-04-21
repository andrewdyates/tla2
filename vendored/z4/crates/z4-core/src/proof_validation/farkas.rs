// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic validation for arithmetic Farkas certificates.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_rational::{BigRational, Rational64};
use num_traits::{One, Zero};
use thiserror::Error;

use crate::{Constant, FarkasAnnotation, Symbol, TermData, TermId, TermStore, TheoryLit};

#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[non_exhaustive]
/// Errors returned when a Farkas certificate fails structural or semantic validation.
pub enum FarkasValidationError {
    /// One or more coefficients were negative, violating the Farkas precondition λ >= 0.
    #[error("Farkas coefficients must be non-negative, but found: {negative:?}")]
    NegativeCoefficients {
        /// `(index, coefficient)` pairs for every negative entry.
        negative: Vec<(usize, Rational64)>,
    },

    /// The number of coefficients does not match the number of conflict literals.
    #[error("Farkas has {coefficients} coefficients but conflict has {literals} literals")]
    CoefficientCountMismatch {
        /// Number of coefficients stored in the certificate.
        coefficients: usize,
        /// Number of theory literals in the conflict being certified.
        literals: usize,
    },

    /// A conflict literal was not an arithmetic atom after stripping `not`.
    #[error("Farkas literal {term:?} is not a binary arithmetic atom")]
    NonArithmeticLiteral {
        /// Term that failed arithmetic-atom decoding.
        term: TermId,
    },

    /// The arithmetic atom used a predicate the verifier does not support.
    #[error("Farkas literal {term:?} has unsupported predicate {predicate}")]
    UnsupportedPredicate {
        /// Term that carried the unsupported predicate.
        term: TermId,
        /// Predicate name found on the arithmetic atom.
        predicate: String,
    },

    /// A disequality-style literal cannot be justified by a Farkas certificate.
    #[error(
        "Farkas certificate references disequality literal {term:?} ({predicate} asserted {value})"
    )]
    DisequalityLiteral {
        /// Term whose predicate is incompatible with Farkas validation.
        term: TermId,
        /// Predicate name found on the arithmetic atom.
        predicate: String,
        /// Boolean value asserted for the predicate.
        value: bool,
    },

    /// The weighted sum left at least one variable coefficient non-zero.
    #[error("Farkas combination does not eliminate variables: coeff({term:?}) = {coefficient}")]
    VariablesNotEliminated {
        /// One surviving variable in the weighted combination.
        term: TermId,
        /// The surviving coefficient for `term`.
        coefficient: BigRational,
    },

    /// The weighted sum reduced to a constant but did not produce contradiction.
    #[error(
        "Farkas combination does not yield contradiction: combined constant = {constant} (needs {expected})"
    )]
    NoContradiction {
        /// Combined constant after eliminating variables.
        constant: BigRational,
        /// Comparison threshold required for contradiction (`> 0` or `>= 0`).
        expected: &'static str,
    },
}

#[derive(Debug, Clone)]
struct LinearExpr {
    coeffs: HashMap<TermId, BigRational>,
    constant: BigRational,
}

impl LinearExpr {
    fn zero() -> Self {
        Self {
            coeffs: HashMap::new(),
            constant: BigRational::zero(),
        }
    }

    fn constant(c: BigRational) -> Self {
        Self {
            coeffs: HashMap::new(),
            constant: c,
        }
    }

    fn var(v: TermId) -> Self {
        let mut coeffs = HashMap::new();
        coeffs.insert(v, BigRational::one());
        Self {
            coeffs,
            constant: BigRational::zero(),
        }
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    fn negate(&mut self) {
        self.constant = -self.constant.clone();
        for coeff in self.coeffs.values_mut() {
            *coeff = -coeff.clone();
        }
    }

    fn scale(&mut self, scale: &BigRational) {
        if scale.is_zero() {
            self.coeffs.clear();
            self.constant = BigRational::zero();
            return;
        }
        if scale.is_one() {
            return;
        }

        self.constant = &self.constant * scale;
        for coeff in self.coeffs.values_mut() {
            *coeff = &*coeff * scale;
        }
    }

    fn add_scaled(&mut self, other: &Self, scale: &BigRational) {
        if scale.is_zero() {
            return;
        }

        self.constant += scale * &other.constant;
        for (var, coeff) in &other.coeffs {
            let should_remove = {
                let entry = self.coeffs.entry(*var).or_insert_with(BigRational::zero);
                *entry += scale * coeff;
                entry.is_zero()
            };
            if should_remove {
                self.coeffs.remove(var);
            }
        }
    }
}

#[derive(Debug, Clone)]
struct NormalizedConstraint {
    /// Normalized as `expr <= 0` if `strict == false`, or `expr < 0` if `strict == true`.
    expr: LinearExpr,
    strict: bool,
}

/// Verify only the structural shape of a Farkas annotation.
///
/// Checks non-negativity of all coefficients and ensures the annotation length
/// matches the number of conflict literals.
pub fn verify_farkas_annotation_shape(
    farkas: &FarkasAnnotation,
    num_literals: usize,
) -> Result<(), FarkasValidationError> {
    if !farkas.is_valid() {
        let negative: Vec<_> = farkas
            .coefficients
            .iter()
            .enumerate()
            .filter(|(_, c)| **c < Rational64::from(0))
            .map(|(idx, coeff)| (idx, *coeff))
            .collect();
        return Err(FarkasValidationError::NegativeCoefficients { negative });
    }

    if farkas.coefficients.len() != num_literals {
        return Err(FarkasValidationError::CoefficientCountMismatch {
            coefficients: farkas.coefficients.len(),
            literals: num_literals,
        });
    }

    Ok(())
}

/// Verify that a Farkas certificate semantically proves an arithmetic conflict.
///
/// The `conflict` slice contains the signed theory literals that are jointly
/// inconsistent. The certificate is valid only if the weighted linear
/// combination eliminates all variables and yields an impossible constant
/// inequality.
pub fn verify_farkas_conflict_lits_full(
    terms: &TermStore,
    conflict: &[TheoryLit],
    farkas: &FarkasAnnotation,
) -> Result<(), FarkasValidationError> {
    verify_farkas_annotation_shape(farkas, conflict.len())?;

    let lambdas: Vec<BigRational> = farkas
        .coefficients
        .iter()
        .map(rational64_to_bigrational)
        .collect();

    let mut alternatives: Vec<Vec<NormalizedConstraint>> = Vec::with_capacity(conflict.len());
    for lit in conflict {
        alternatives.push(normalized_constraint_alternatives(
            terms, lit.term, lit.value,
        )?);
    }

    // Compute total search space: product of alternative counts per literal.
    // Equality literals produce 2 alternatives each; the search function
    // explores all combinations, giving O(2^n) for n equalities.  Cap the
    // search to avoid exponential blowup in conflicts with many equalities
    // (#W16-5: was the dominant cost — 42% of solver time on QF_LRA benchmarks).
    let search_space: u64 = alternatives
        .iter()
        .map(|a| a.len() as u64)
        .try_fold(1u64, u64::checked_mul)
        .unwrap_or(u64::MAX);

    if search_space <= 1024 {
        if search(0, &alternatives, &lambdas, &LinearExpr::zero(), false) {
            return Ok(());
        }
    } else {
        // Too many combinations — try only the first alternative for each
        // literal (fast path).  If that succeeds, accept the certificate.
        let mut sum = LinearExpr::zero();
        let mut strict = false;
        for (alts, lambda) in alternatives.iter().zip(lambdas.iter()) {
            let alt = &alts[0];
            sum.add_scaled(&alt.expr, lambda);
            strict = strict || (!lambda.is_zero() && alt.strict);
        }
        if is_contradiction(&sum, strict) {
            return Ok(());
        }
        // Try the second alternative for each equality literal one at a time
        for i in 0..alternatives.len() {
            if alternatives[i].len() <= 1 {
                continue;
            }
            let mut sum2 = LinearExpr::zero();
            let mut strict2 = false;
            for (j, (alts, lambda)) in alternatives.iter().zip(lambdas.iter()).enumerate() {
                let alt_idx = if j == i { 1 } else { 0 };
                let alt = &alts[alt_idx.min(alts.len() - 1)];
                sum2.add_scaled(&alt.expr, lambda);
                strict2 = strict2 || (!lambda.is_zero() && alt.strict);
            }
            if is_contradiction(&sum2, strict2) {
                return Ok(());
            }
        }
    }

    // Fallback: compute error diagnostics using first alternative only
    let mut sum = LinearExpr::zero();
    let mut strict = false;
    for (alts, lambda) in alternatives.iter().zip(lambdas.iter()) {
        let alt = &alts[0];
        sum.add_scaled(&alt.expr, lambda);
        strict = strict || (!lambda.is_zero() && alt.strict);
    }

    if let Some((term, coefficient)) = sum.coeffs.iter().find(|(_, coeff)| !coeff.is_zero()) {
        return Err(FarkasValidationError::VariablesNotEliminated {
            term: *term,
            coefficient: coefficient.clone(),
        });
    }

    Err(FarkasValidationError::NoContradiction {
        constant: sum.constant,
        expected: if strict { ">= 0" } else { "> 0" },
    })
}

fn rational64_to_bigrational(r: &Rational64) -> BigRational {
    BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
}

fn parse_linear_expr(terms: &TermStore, term: TermId) -> LinearExpr {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => LinearExpr::constant(BigRational::from(n.clone())),
        TermData::Const(Constant::Rational(r)) => LinearExpr::constant(r.0.clone()),
        TermData::Var(_, _) => LinearExpr::var(term),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                let mut result = LinearExpr::zero();
                for &arg in args {
                    let sub = parse_linear_expr(terms, arg);
                    result.add_scaled(&sub, &BigRational::one());
                }
                result
            }
            "-" if args.len() == 1 => {
                let mut result = parse_linear_expr(terms, args[0]);
                result.negate();
                result
            }
            "-" if args.len() >= 2 => {
                let mut result = parse_linear_expr(terms, args[0]);
                for &arg in &args[1..] {
                    let mut sub = parse_linear_expr(terms, arg);
                    sub.negate();
                    result.add_scaled(&sub, &BigRational::one());
                }
                result
            }
            "*" => {
                let mut const_part = BigRational::one();
                let mut non_const: Option<LinearExpr> = None;

                for &arg in args {
                    let sub = parse_linear_expr(terms, arg);
                    if sub.is_constant() {
                        const_part *= sub.constant;
                    } else if non_const.is_none() {
                        non_const = Some(sub);
                    } else {
                        return LinearExpr::var(term);
                    }
                }

                match non_const {
                    Some(mut expr) => {
                        expr.scale(&const_part);
                        expr
                    }
                    None => LinearExpr::constant(const_part),
                }
            }
            "/" if args.len() == 2 => {
                let mut numerator = parse_linear_expr(terms, args[0]);
                let denominator = parse_linear_expr(terms, args[1]);
                if denominator.is_constant() && !denominator.constant.is_zero() {
                    let inv = BigRational::one() / denominator.constant;
                    numerator.scale(&inv);
                    numerator
                } else {
                    LinearExpr::var(term)
                }
            }
            _ => LinearExpr::var(term),
        },
        TermData::App(_, _) => LinearExpr::var(term),
        _ => LinearExpr::var(term),
    }
}

fn normalized_constraint_alternatives(
    terms: &TermStore,
    mut term: TermId,
    mut value: bool,
) -> Result<Vec<NormalizedConstraint>, FarkasValidationError> {
    while let TermData::Not(inner) = terms.get(term) {
        term = *inner;
        value = !value;
    }

    let (pred, lhs, rhs) = match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
            (name.as_str(), args[0], args[1])
        }
        _ => return Err(FarkasValidationError::NonArithmeticLiteral { term }),
    };

    let (mut base_expr, base_strict, is_equality_like) = match pred {
        "<" => {
            let mut expr = parse_linear_expr(terms, lhs);
            let rhs_expr = parse_linear_expr(terms, rhs);
            expr.add_scaled(&rhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, true, false)
        }
        "<=" => {
            let mut expr = parse_linear_expr(terms, lhs);
            let rhs_expr = parse_linear_expr(terms, rhs);
            expr.add_scaled(&rhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, false, false)
        }
        ">" => {
            let mut expr = parse_linear_expr(terms, rhs);
            let lhs_expr = parse_linear_expr(terms, lhs);
            expr.add_scaled(&lhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, true, false)
        }
        ">=" => {
            let mut expr = parse_linear_expr(terms, rhs);
            let lhs_expr = parse_linear_expr(terms, lhs);
            expr.add_scaled(&lhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, false, false)
        }
        "=" | "distinct" => {
            let mut expr = parse_linear_expr(terms, lhs);
            let rhs_expr = parse_linear_expr(terms, rhs);
            expr.add_scaled(&rhs_expr, &BigRational::from(BigInt::from(-1)));
            (expr, false, true)
        }
        _ => {
            return Err(FarkasValidationError::UnsupportedPredicate {
                term,
                predicate: pred.to_string(),
            });
        }
    };

    if is_equality_like {
        let equality_holds = (pred == "=" && value) || (pred == "distinct" && !value);
        if !equality_holds {
            return Err(FarkasValidationError::DisequalityLiteral {
                term,
                predicate: pred.to_string(),
                value,
            });
        }

        let mut neg = base_expr.clone();
        neg.negate();
        return Ok(vec![
            NormalizedConstraint {
                expr: base_expr,
                strict: false,
            },
            NormalizedConstraint {
                expr: neg,
                strict: false,
            },
        ]);
    }

    if !value {
        base_expr.negate();
    }
    let strict = if value { base_strict } else { !base_strict };

    Ok(vec![NormalizedConstraint {
        expr: base_expr,
        strict,
    }])
}

fn is_contradiction(sum: &LinearExpr, strict: bool) -> bool {
    if !sum.coeffs.is_empty() {
        return false;
    }
    if strict {
        sum.constant >= BigRational::zero()
    } else {
        sum.constant > BigRational::zero()
    }
}

fn search(
    idx: usize,
    alternatives: &[Vec<NormalizedConstraint>],
    lambdas: &[BigRational],
    acc: &LinearExpr,
    strict_acc: bool,
) -> bool {
    if idx == alternatives.len() {
        return is_contradiction(acc, strict_acc);
    }

    let lambda = &lambdas[idx];
    let candidates: &[NormalizedConstraint] = if lambda.is_zero() {
        &alternatives[idx][0..1]
    } else {
        &alternatives[idx]
    };

    for alt in candidates {
        let mut next = acc.clone();
        next.add_scaled(&alt.expr, lambda);
        let next_strict = strict_acc || (!lambda.is_zero() && alt.strict);
        if search(idx + 1, alternatives, lambdas, &next, next_strict) {
            return true;
        }
    }

    false
}

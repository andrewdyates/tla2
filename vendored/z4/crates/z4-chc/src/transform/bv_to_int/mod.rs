// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV-to-Int abstraction for CHC problems (#5981).
//!
//! Converts BV-sorted predicates and operations to integer arithmetic,
//! enabling Z4's LIA invariant discovery to synthesize invariants for BV CHC problems.
//!
//! Soundness: the exact mode encodes bvadd/bvsub/bvmul with modular arithmetic
//! and range constraints, so Safe results transfer back to the original BV
//! problem. The legacy relaxed mode is retained only for tests/experiments and
//! is unsound for Safe proofs because signed overflow changes reachability
//! (#6848).

mod ops;
#[cfg(test)]
mod tests;

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};

use crate::smt::SmtValue;
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PredicateId, PredicateInterpretation,
};
use rustc_hash::FxHashMap;

use super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformationResult, Transformer,
    ValidityWitness,
};

/// Tracks BV↔Int mapping for back-translation.
pub(crate) struct BvIntMap {
    /// Per-predicate: argument index -> original BV width (None if not BV).
    pred_arg_widths: FxHashMap<PredicateId, Vec<Option<u32>>>,
    /// Per-predicate original argument sorts, used to concretize invalidity witnesses.
    pred_arg_sorts: FxHashMap<PredicateId, Vec<ChcSort>>,
    uf_counter: u32,
    /// Set to true if any BV constant overflows i64 during abstraction.
    /// When true, the entire BV-to-Int transformation is aborted and the
    /// original problem is returned unchanged (#7548).
    has_overflow: bool,
}

impl BvIntMap {
    fn new() -> Self {
        Self {
            pred_arg_widths: FxHashMap::default(),
            pred_arg_sorts: FxHashMap::default(),
            uf_counter: 0,
            has_overflow: false,
        }
    }

    fn next_uf_name(&mut self, base: &str, width: u32) -> String {
        self.uf_counter += 1;
        format!("__bv2int_{base}_{}_w{width}", self.uf_counter)
    }
}

/// BV-to-Int abstraction transformer. No-op for non-BV problems.
pub(crate) struct BvToIntAbstractor {
    verbose: bool,
    /// Legacy experimental mode. When true, BV arithmetic is mapped to
    /// unbounded integer arithmetic without modular wrapping. This is UNSOUND
    /// for Safe proofs under signed overflow and must not be used in
    /// production solving paths (#6848).
    relaxed: bool,
}

impl BvToIntAbstractor {
    pub(crate) fn new() -> Self {
        Self {
            verbose: false,
            relaxed: false,
        }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Enable relaxed mode: unbounded integer arithmetic without modular
    /// wrapping. Callers MUST validate Safe results against the original BV
    /// problem before accepting them (#4198, #6848).
    pub(crate) fn with_relaxed(mut self, relaxed: bool) -> Self {
        self.relaxed = relaxed;
        self
    }

    /// Create a relaxed BvToInt abstractor for unit tests.
    #[cfg(test)]
    pub(crate) fn relaxed() -> Self {
        Self::new().with_relaxed(true)
    }
}

fn sort_contains_bv(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::BitVec(_) => true,
        ChcSort::Array(key, value) => sort_contains_bv(key) || sort_contains_bv(value),
        ChcSort::Bool
        | ChcSort::Int
        | ChcSort::Real
        | ChcSort::Uninterpreted(_)
        | ChcSort::Datatype { .. } => false,
    }
}

fn problem_contains_recursive_bv_sorts(problem: &ChcProblem) -> bool {
    problem
        .predicates()
        .iter()
        .flat_map(|pred| pred.arg_sorts.iter())
        .any(sort_contains_bv)
}

impl Transformer for BvToIntAbstractor {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if !problem_contains_recursive_bv_sorts(&problem) {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        let mut map = BvIntMap::new();
        let transformed = abstract_problem(&problem, &mut map, self.verbose, self.relaxed);
        // If any BV constant overflowed i64, the transformation produced wrong
        // integer values. Abort and return the original BV problem so that the
        // solver falls back to other strategies (#7548).
        if map.has_overflow {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        TransformationResult {
            problem: transformed,
            back_translator: Box::new(BvIntBackTranslator { map }),
        }
    }
}

// ── Core abstraction ──────────────────────────────────────────────────────

fn abstract_problem(
    problem: &ChcProblem,
    map: &mut BvIntMap,
    _verbose: bool,
    relaxed: bool,
) -> ChcProblem {
    let mut result = ChcProblem::new();

    // Convert predicate signatures: BV(w) → Int, recording widths.
    // Array sub-sorts are also recursively abstracted: Array(BV(32), Bool)
    // becomes Array(Int, Bool) so that sort annotations match abstracted
    // expressions throughout the problem (#6122).
    for pred in problem.predicates() {
        let mut widths = Vec::with_capacity(pred.arg_sorts.len());
        let sorts: Vec<ChcSort> = pred
            .arg_sorts
            .iter()
            .map(|s| match s {
                ChcSort::BitVec(w) => {
                    widths.push(Some(*w));
                    ChcSort::Int
                }
                other => {
                    widths.push(None);
                    ops::abstract_sort(other)
                }
            })
            .collect();
        let pid = result.declare_predicate(&pred.name, sorts);
        map.pred_arg_widths.insert(pid, widths);
        map.pred_arg_sorts.insert(pid, pred.arg_sorts.clone());
    }

    // Abstract each clause
    let abs = |e: &ChcExpr, m: &mut BvIntMap| abstract_expr(e, m, relaxed);
    for clause in problem.clauses() {
        let body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
            .body
            .predicates
            .iter()
            .map(|(pid, args)| {
                let abs_args: Vec<ChcExpr> = args.iter().map(|a| abs(a, map)).collect();
                (*pid, abs_args)
            })
            .collect();

        let body_constraint = clause.body.constraint.as_ref().map(|c| abs(c, map));

        let head = match &clause.head {
            ClauseHead::Predicate(pid, args) => {
                let abs_args = args.iter().map(|a| abs(a, map)).collect();
                ClauseHead::Predicate(*pid, abs_args)
            }
            ClauseHead::False => ClauseHead::False,
        };

        let body = ClauseBody::new(body_preds, body_constraint);
        result.add_clause(HornClause::new(body, head));
    }

    // In relaxed mode, skip range constraints and treat BV as unbounded Int.
    // This mode is retained only for tests/experiments; it is unsound for Safe
    // proofs because BV overflow is not preserved (#6848).
    if !relaxed {
        collect_range_constraints(&mut result, map);
    }
    result
}

/// Embed BV range constraints into existing clause head arguments.
///
/// Instead of adding identity clauses `P(x) => P(x) ∧ 0≤x<2^w` (which create
/// duplicate head definitions and block clause inlining), this adds range
/// constraints directly to each clause that defines a predicate with BV-converted
/// Int arguments. For a clause `body => P(a1, ..., an)`, if `ai` was originally
/// `BitVec(w)`, we add `0 <= ai < 2^w` to the body constraint.
fn collect_range_constraints(result: &mut ChcProblem, map: &BvIntMap) {
    let clauses = result.clauses().to_vec();
    // Clear and re-add clauses with embedded range constraints
    *result = {
        let mut new_problem = ChcProblem::new();
        for pred in result.predicates() {
            new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
        }
        for clause in &clauses {
            let range_constraints = match &clause.head {
                ClauseHead::Predicate(pid, head_args) => {
                    if let Some(widths) = map.pred_arg_widths.get(pid) {
                        let mut ranges = Vec::new();
                        for (w_opt, arg) in widths.iter().zip(head_args.iter()) {
                            if let Some(w) = w_opt {
                                // #7006: Skip range constraints for BV widths >= 63.
                                // The exact modular encoding (bvadd uses ITE wrapping,
                                // bvmul uses mod) already guarantees values in [0, 2^w).
                                // For BV64, the upper bound 2^64 causes Rational64
                                // overflow in the LRA solver (i64::MAX as numerator).
                                if *w >= 63 {
                                    continue;
                                }
                                let bound = ops::int_pow2(*w);
                                let expr = arg.clone();
                                ranges.push(ChcExpr::and(
                                    ChcExpr::ge(expr.clone(), ChcExpr::int(0)),
                                    ChcExpr::lt(expr, bound),
                                ));
                            }
                        }
                        ranges
                    } else {
                        Vec::new()
                    }
                }
                ClauseHead::False => Vec::new(),
            };

            if range_constraints.is_empty() {
                new_problem.add_clause(clause.clone());
            } else {
                // Combine existing body constraint with range constraints
                let mut all_constraints: Vec<ChcExpr> = Vec::new();
                if let Some(c) = &clause.body.constraint {
                    all_constraints.push(c.clone());
                }
                all_constraints.extend(range_constraints);
                let combined = all_constraints
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .expect("non-empty");
                let new_body = ClauseBody::new(clause.body.predicates.clone(), Some(combined));
                new_problem.add_clause(HornClause::new(new_body, clause.head.clone()));
            }
        }
        new_problem
    };
}

fn abstract_expr(expr: &ChcExpr, map: &mut BvIntMap, relaxed: bool) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::BitVec(val, w) => {
            if relaxed {
                // In relaxed mode, signed comparisons (bvsle, bvslt, etc.) are mapped
                // to plain <=/<. For this to be semantically correct, BV constants must
                // use their signed interpretation. E.g. #xffffffff (32-bit) = -1, not
                // 4294967295. Without this, (bvsle #xffffffff #x00000000) would become
                // (4294967295 <= 0) = false instead of (-1 <= 0) = true. (#5877)
                let half = 1u128 << (w - 1);
                if *val >= half {
                    // Negative signed value: val - 2^w
                    let signed = (*val as i128) - (1i128 << w);
                    match i64::try_from(signed) {
                        Ok(v) => ChcExpr::int(v),
                        Err(_) => {
                            map.has_overflow = true;
                            ChcExpr::int(0)
                        }
                    }
                } else {
                    match i64::try_from(*val) {
                        Ok(v) => ChcExpr::int(v),
                        Err(_) => {
                            map.has_overflow = true;
                            ChcExpr::int(0)
                        }
                    }
                }
            } else {
                // In exact mode, BV values are unsigned [0, 2^w) and signed comparisons
                // use explicit offset subtraction (signed_cmp helper in ops.rs).
                match i64::try_from(*val) {
                    Ok(v) => ChcExpr::int(v),
                    Err(_) => {
                        // #7006: BV64 values >= 2^63 don't fit in i64.
                        // Represent as (low + high * 2^32) where both halves fit in i64.
                        // This avoids aborting the entire BvToInt transformation.
                        let low = (*val & 0xFFFF_FFFF) as i64;
                        let high = (*val >> 32) as i64;
                        if high == 0 {
                            ChcExpr::int(low)
                        } else if low == 0 {
                            ChcExpr::mul(ChcExpr::int(high), ChcExpr::int(1i64 << 32))
                        } else {
                            ChcExpr::add(
                                ChcExpr::int(low),
                                ChcExpr::mul(ChcExpr::int(high), ChcExpr::int(1i64 << 32)),
                            )
                        }
                    }
                }
            }
        }
        ChcExpr::Var(v) => {
            // Abstract variable sort: BV(w) → Int, and recursively abstract
            // compound sorts like Array(BV(w), V) → Array(Int, V) (#6122).
            let abs_sort = ops::abstract_sort(&v.sort);
            if abs_sort == v.sort {
                expr.clone()
            } else {
                ChcExpr::Var(ChcVar::new(v.name.clone(), abs_sort))
            }
        }
        ChcExpr::Op(op, args) => {
            let aa: Vec<ChcExpr> = args
                .iter()
                .map(|a| abstract_expr(a, map, relaxed))
                .collect();
            if relaxed {
                ops::abstract_op_relaxed(op, args, aa, map)
            } else {
                ops::abstract_op(op, args, aa, map)
            }
        }
        ChcExpr::PredicateApp(name, id, args) => ChcExpr::PredicateApp(
            name.clone(),
            *id,
            args.iter()
                .map(|a| Arc::new(abstract_expr(a, map, relaxed)))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            ops::abstract_sort(sort),
            args.iter()
                .map(|a| Arc::new(abstract_expr(a, map, relaxed)))
                .collect(),
        ),
        ChcExpr::ConstArray(ks, val) => {
            // Recursively abstract the key sort: Array(BV(w), V) → Array(Int, V) (#6122)
            ChcExpr::ConstArray(
                ops::abstract_sort(ks),
                Arc::new(abstract_expr(val, map, relaxed)),
            )
        }
        _ => expr.clone(),
    })
}

// ── Back-translation ───────────────────────────────────────────────────────

struct BvIntBackTranslator {
    map: BvIntMap,
}

impl BackTranslator for BvIntBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        concretize_inv(&witness, &self.map)
    }
    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        concretize_cex(witness, &self.map)
    }
}

fn concretize_inv(inv: &InvariantModel, map: &BvIntMap) -> InvariantModel {
    let mut result = InvariantModel::new();
    for (pid, interp) in inv.iter() {
        let orig_sorts = map.pred_arg_sorts.get(pid);
        let widths = map.pred_arg_widths.get(pid);
        let vars: Vec<ChcVar> = interp
            .vars
            .iter()
            .enumerate()
            .map(|(i, v)| {
                // First try: restore BV sort from widths (direct BV args).
                if let Some(w) = widths.and_then(|ws| ws.get(i).copied().flatten()) {
                    return ChcVar::new(v.name.clone(), ChcSort::BitVec(w));
                }
                // Second try: restore original sort (handles Array(BV, _) -> Array(Int, _)).
                if let Some(orig) = orig_sorts.and_then(|ss| ss.get(i)) {
                    if *orig != v.sort {
                        return ChcVar::new(v.name.clone(), orig.clone());
                    }
                }
                v.clone()
            })
            .collect();
        // Build sort environment mapping the *old* (Int-sorted) variables from the
        // abstract formula to their *new* (restored) sorts. The formula still
        // contains the old variable identities, so the lookup key must match those.
        // Clause-inlining back-translation can synthesize formulas that contain
        // clause-local variables sharing a name with a predicate parameter but
        // having a different sort. By keying on the old full variable identity
        // (not just name), we avoid turning array locals into BV scalars.
        let sort_env: FxHashMap<ChcVar, ChcSort> = interp
            .vars
            .iter()
            .zip(vars.iter())
            .filter(|(old, new)| old.sort != new.sort)
            .map(|(old, new)| (old.clone(), new.sort.clone()))
            .collect();
        // Transform the formula: convert Int constants to BV where context
        // demands it (e.g., array indices, BV comparisons).
        let formula = int_to_bv_formula(&interp.formula, &sort_env).simplify_constants();
        result.set(*pid, PredicateInterpretation::new(vars, formula));
    }
    result.verification_method = inv.verification_method;
    result
}

/// Recursively restore original sorts while preserving abstract Int semantics.
///
/// A validity witness from the BV-to-Int abstraction is still an Int formula:
/// former BV variables denote their unsigned numeric values. Back-translation
/// therefore restores the original variable sorts but keeps arithmetic and
/// comparisons in the Int domain, bridging restored BV terms with `bv2nat` /
/// `int2bv` as needed. Rewriting learned Int arithmetic back into native BV
/// arithmetic would reintroduce modular wrapping and change the witness.
fn int_to_bv_formula(expr: &ChcExpr, sort_env: &FxHashMap<ChcVar, ChcSort>) -> ChcExpr {
    match expr {
        // Variables: update sort from environment.
        ChcExpr::Var(v) => {
            if let Some(new_sort) = sort_env.get(v) {
                if *new_sort != v.sort {
                    return ChcExpr::var(ChcVar::new(v.name.clone(), new_sort.clone()));
                }
            }
            expr.clone()
        }
        // Int constants: may need conversion to BV if used in BV context.
        // Leave as-is here; parent operations handle context-driven conversion.
        ChcExpr::Int(_) | ChcExpr::Bool(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
            expr.clone()
        }
        ChcExpr::Op(op, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| int_to_bv_formula(a, sort_env))
                .collect();
            match op {
                // Select: convert Int index to BV if array has BV index sort.
                ChcOp::Select if new_args.len() == 2 => {
                    let arr = &new_args[0];
                    let idx = &new_args[1];
                    if let ChcSort::Array(idx_sort, _) = arr.sort() {
                        let idx = coerce_to_sort(idx, &idx_sort);
                        return ChcExpr::select(arr.clone(), idx);
                    }
                    ChcExpr::select(arr.clone(), idx.clone())
                }
                // Store: convert Int index and value to BV sorts if needed.
                ChcOp::Store if new_args.len() == 3 => {
                    let arr = &new_args[0];
                    let idx = &new_args[1];
                    let val = &new_args[2];
                    if let ChcSort::Array(idx_sort, val_sort) = arr.sort() {
                        let idx = coerce_to_sort(idx, &idx_sort);
                        let val = coerce_to_sort(val, &val_sort);
                        return ChcExpr::store(arr.clone(), idx, val);
                    }
                    ChcExpr::store(arr.clone(), idx.clone(), val.clone())
                }
                // Equality/comparisons: keep the abstract Int semantics.
                ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                    if new_args.len() == 2 =>
                {
                    let a = &new_args[0];
                    let b = &new_args[1];
                    if let Some(translated) = translate_bv_int_comparison(op, a, b) {
                        return translated;
                    }
                    match (a.sort(), b.sort()) {
                        (ChcSort::BitVec(_), _) | (_, ChcSort::BitVec(_)) => {
                            let a = coerce_to_sort(a, &ChcSort::Int);
                            let b = coerce_to_sort(b, &ChcSort::Int);
                            ChcExpr::Op(op.clone(), vec![Arc::new(a), Arc::new(b)])
                        }
                        _ => ChcExpr::Op(op.clone(), new_args.into_iter().map(Arc::new).collect()),
                    }
                }
                // Arithmetic: preserve the learned Int arithmetic and lift
                // restored BV terms through `bv2nat`.
                ChcOp::Add | ChcOp::Sub | ChcOp::Mul | ChcOp::Mod | ChcOp::Div
                    if new_args.len() == 2
                        && (matches!(new_args[0].sort(), ChcSort::BitVec(_))
                            || matches!(new_args[1].sort(), ChcSort::BitVec(_))) =>
                {
                    let a = coerce_to_sort(&new_args[0], &ChcSort::Int);
                    let b = coerce_to_sort(&new_args[1], &ChcSort::Int);
                    ChcExpr::Op(op.clone(), vec![Arc::new(a), Arc::new(b)])
                }
                _ => ChcExpr::Op(op.clone(), new_args.into_iter().map(Arc::new).collect()),
            }
        }
        // Predicate/func applications: recurse into args.
        ChcExpr::PredicateApp(name, sort, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| Arc::new(int_to_bv_formula(a, sort_env)))
                .collect();
            ChcExpr::PredicateApp(name.clone(), *sort, new_args)
        }
        ChcExpr::FuncApp(name, sort, args) => {
            let new_args: Vec<_> = args
                .iter()
                .map(|a| Arc::new(int_to_bv_formula(a, sort_env)))
                .collect();
            ChcExpr::FuncApp(name.clone(), sort.clone(), new_args)
        }
        ChcExpr::ConstArray(sort, val) => {
            ChcExpr::ConstArray(sort.clone(), Arc::new(int_to_bv_formula(val, sort_env)))
        }
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => expr.clone(),
    }
}

fn translate_bv_int_comparison(op: &ChcOp, lhs: &ChcExpr, rhs: &ChcExpr) -> Option<ChcExpr> {
    if let ChcSort::BitVec(width) = lhs.sort() {
        return Some(translate_unsigned_bv_comparison(
            op,
            lhs,
            &try_const_bigint(rhs)?,
            width,
        ));
    }
    if let ChcSort::BitVec(width) = rhs.sort() {
        return Some(translate_unsigned_bv_comparison(
            &reverse_comparison(op),
            rhs,
            &try_const_bigint(lhs)?,
            width,
        ));
    }
    None
}

fn translate_unsigned_bv_comparison(
    op: &ChcOp,
    bv_expr: &ChcExpr,
    int_value: &BigInt,
    width: u32,
) -> ChcExpr {
    let zero = BigInt::from(0u8);
    let max = max_unsigned_bv(width);
    if int_value < &zero {
        return match op {
            ChcOp::Eq => ChcExpr::Bool(false),
            ChcOp::Ne => ChcExpr::Bool(true),
            ChcOp::Lt | ChcOp::Le => ChcExpr::Bool(false),
            ChcOp::Gt | ChcOp::Ge => ChcExpr::Bool(true),
            _ => unreachable!("translate_unsigned_bv_comparison only handles comparisons"),
        };
    }
    if int_value > &max {
        return match op {
            ChcOp::Eq => ChcExpr::Bool(false),
            ChcOp::Ne => ChcExpr::Bool(true),
            ChcOp::Lt | ChcOp::Le => ChcExpr::Bool(true),
            ChcOp::Gt | ChcOp::Ge => ChcExpr::Bool(false),
            _ => unreachable!("translate_unsigned_bv_comparison only handles comparisons"),
        };
    }
    if int_value == &zero {
        return match op {
            ChcOp::Lt => ChcExpr::Bool(false),
            ChcOp::Ge => ChcExpr::Bool(true),
            _ => build_unsigned_bv_comparison(op, bv_expr, int_value, width),
        };
    }
    if int_value == &max {
        return match op {
            ChcOp::Le => ChcExpr::Bool(true),
            ChcOp::Gt => ChcExpr::Bool(false),
            _ => build_unsigned_bv_comparison(op, bv_expr, int_value, width),
        };
    }

    build_unsigned_bv_comparison(op, bv_expr, int_value, width)
}

fn build_unsigned_bv_comparison(
    op: &ChcOp,
    bv_expr: &ChcExpr,
    int_value: &BigInt,
    width: u32,
) -> ChcExpr {
    let rhs = ChcExpr::BitVec(
        int_value
            .to_u128()
            .expect("in-range BV comparison constants must fit in u128"),
        width,
    );
    ChcExpr::Op(
        int_cmp_to_bv(op),
        vec![Arc::new(bv_expr.clone()), Arc::new(rhs)],
    )
}

fn max_unsigned_bv(width: u32) -> BigInt {
    (BigInt::one() << width) - BigInt::one()
}

fn try_const_bigint(expr: &ChcExpr) -> Option<BigInt> {
    match expr {
        ChcExpr::Int(value) => Some(BigInt::from(*value)),
        ChcExpr::Op(ChcOp::Add, args) => args.iter().try_fold(BigInt::from(0u8), |acc, arg| {
            Some(acc + try_const_bigint(arg)?)
        }),
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut args = args.iter();
            let first = try_const_bigint(args.next()?)?;
            args.try_fold(first, |acc, arg| Some(acc - try_const_bigint(arg)?))
        }
        ChcExpr::Op(ChcOp::Mul, args) => args
            .iter()
            .try_fold(BigInt::one(), |acc, arg| Some(acc * try_const_bigint(arg)?)),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => Some(-try_const_bigint(&args[0])?),
        _ => None,
    }
}

fn reverse_comparison(op: &ChcOp) -> ChcOp {
    match op {
        ChcOp::Eq => ChcOp::Eq,
        ChcOp::Ne => ChcOp::Ne,
        ChcOp::Lt => ChcOp::Gt,
        ChcOp::Le => ChcOp::Ge,
        ChcOp::Gt => ChcOp::Lt,
        ChcOp::Ge => ChcOp::Le,
        _ => unreachable!("reverse_comparison only handles comparisons"),
    }
}

/// Coerce an expression to a target sort for back-translation.
fn coerce_to_sort(expr: &ChcExpr, target: &ChcSort) -> ChcExpr {
    match (expr, target) {
        (expr, ChcSort::Int) if matches!(expr.sort(), ChcSort::BitVec(_)) => {
            ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(expr.clone())])
        }
        (ChcExpr::Int(n), ChcSort::BitVec(w)) => {
            // Convert Int to BV: take the value modulo 2^w.
            if *w >= 64 {
                // For wide BV, use u128 arithmetic.
                let modulus = 1u128 << w;
                let bits = if *n >= 0 {
                    (*n as u128) % modulus
                } else {
                    let abs = (-*n) as u128;
                    (modulus - (abs % modulus)) % modulus
                };
                return ChcExpr::BitVec(bits, *w);
            }
            let modulus = 1u64 << w;
            let bits = if *n >= 0 {
                (*n as u64) % modulus
            } else {
                let abs = (-*n) as u64;
                (modulus - (abs % modulus)) % modulus
            };
            ChcExpr::BitVec(bits as u128, *w)
        }
        (expr, ChcSort::BitVec(w)) if matches!(expr.sort(), ChcSort::Int) => {
            ChcExpr::Op(ChcOp::Int2Bv(*w), vec![Arc::new(expr.clone())])
        }
        _ if expr.sort() == *target => expr.clone(),
        _ => expr.clone(),
    }
}

/// Convert Int comparison op to unsigned BV comparison.
fn int_cmp_to_bv(op: &ChcOp) -> ChcOp {
    match op {
        ChcOp::Eq => ChcOp::Eq,
        ChcOp::Ne => ChcOp::Ne,
        ChcOp::Lt => ChcOp::BvULt,
        ChcOp::Le => ChcOp::BvULe,
        ChcOp::Gt => ChcOp::BvUGt,
        ChcOp::Ge => ChcOp::BvUGe,
        other => other.clone(),
    }
}

fn concretize_cex(mut cex: InvalidityWitness, map: &BvIntMap) -> InvalidityWitness {
    if let Some(witness) = &mut cex.witness {
        for entry in &mut witness.entries {
            concretize_witness_entry(entry, map);
        }
    }
    cex
}

fn concretize_witness_entry(
    entry: &mut crate::pdr::counterexample::DerivationWitnessEntry,
    map: &BvIntMap,
) {
    let Some(arg_sorts) = map.pred_arg_sorts.get(&entry.predicate) else {
        return;
    };

    for (arg_idx, sort) in arg_sorts.iter().enumerate() {
        let canonical_name = format!("__p{}_a{}", entry.predicate.index(), arg_idx);
        if let Some(value) = entry.instances.get_mut(&canonical_name) {
            *value = concretize_smt_value(value, sort);
        }
    }
}

fn concretize_smt_value(value: &SmtValue, sort: &ChcSort) -> SmtValue {
    match (sort, value) {
        (ChcSort::BitVec(width), SmtValue::Int(n)) => {
            SmtValue::BitVec(int_to_bitvec_bits(*n, *width), *width)
        }
        (ChcSort::BitVec(width), SmtValue::BitVec(bits, actual_width)) if width == actual_width => {
            SmtValue::BitVec(*bits, *width)
        }
        (ChcSort::BitVec(width), SmtValue::BitVec(bits, _)) => {
            SmtValue::BitVec(mask_bitvec_bits(*bits, *width), *width)
        }
        (ChcSort::Array(_index_sort, element_sort), SmtValue::ConstArray(default)) => {
            SmtValue::ConstArray(Box::new(concretize_smt_value(
                default,
                element_sort.as_ref(),
            )))
        }
        (ChcSort::Array(index_sort, element_sort), SmtValue::ArrayMap { default, entries }) => {
            let translated_entries = entries
                .iter()
                .map(|(idx, val)| {
                    (
                        concretize_smt_value(idx, index_sort.as_ref()),
                        concretize_smt_value(val, element_sort.as_ref()),
                    )
                })
                .collect();
            SmtValue::ArrayMap {
                default: Box::new(concretize_smt_value(default, element_sort.as_ref())),
                entries: translated_entries,
            }
        }
        _ => value.clone(),
    }
}

fn int_to_bitvec_bits(value: i64, width: u32) -> u128 {
    if width >= 128 {
        (i128::from(value)) as u128
    } else {
        let modulus = 1i128 << width;
        (i128::from(value).rem_euclid(modulus)) as u128
    }
}

fn mask_bitvec_bits(value: u128, width: u32) -> u128 {
    if width >= 128 {
        value
    } else {
        value & ((1u128 << width) - 1)
    }
}

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, ChcVar};

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

#[test]
fn test_small_model_evaluate_int() {
    let mut int_assignments = FxHashMap::default();
    int_assignments.insert("x".to_string(), 5);
    int_assignments.insert("y".to_string(), 3);
    let model = SmallModel {
        int_assignments,
        bool_assignments: FxHashMap::default(),
    };
    let x = ChcExpr::var(int_var("x"));
    let y = ChcExpr::var(int_var("y"));
    assert_eq!(
        model.evaluate_int(&ChcExpr::add(x.clone(), y.clone())),
        Some(8)
    );
    assert_eq!(
        model.evaluate(&ChcExpr::gt(x.clone(), y.clone())),
        Some(true)
    );
    assert_eq!(model.evaluate(&ChcExpr::lt(x, y)), Some(false));
}

#[test]
fn test_small_model_evaluate_int_euclidean_div() {
    use std::sync::Arc;

    // SMT-LIB div is Euclidean: result rounds toward -infinity, remainder is non-negative.
    let mut int_assignments = FxHashMap::default();
    int_assignments.insert("a".to_string(), -7);
    int_assignments.insert("b".to_string(), 2);
    int_assignments.insert("c".to_string(), 7);
    int_assignments.insert("d".to_string(), -2);
    let model = SmallModel {
        int_assignments,
        bool_assignments: FxHashMap::default(),
    };
    let a = ChcExpr::var(int_var("a"));
    let b = ChcExpr::var(int_var("b"));
    let c = ChcExpr::var(int_var("c"));
    let d = ChcExpr::var(int_var("d"));

    // div(-7, 2) = -4 (Euclidean), not -3 (truncation)
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(a.clone()), Arc::new(b.clone())]
        )),
        Some(-4)
    );
    // div(7, -2) = -3
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(c), Arc::new(d.clone())]
        )),
        Some(-3)
    );
    // div(-7, -2) = 4 (Euclidean), not 3 (truncation)
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(a.clone()), Arc::new(d)]
        )),
        Some(4)
    );
    // mod(-7, 2) = 1 (Euclidean, always non-negative), not -1 (truncation)
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(
            ChcOp::Mod,
            vec![Arc::new(a.clone()), Arc::new(b)]
        )),
        Some(1)
    );
    // div by zero returns None
    let zero = ChcExpr::int(0);
    assert_eq!(
        model.evaluate_int(&ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(zero)])),
        None
    );
}

#[test]
fn test_small_model_from_smt_model() {
    let mut smt_model = FxHashMap::default();
    smt_model.insert("a".to_string(), SmtValue::Int(10));
    smt_model.insert("b".to_string(), SmtValue::Bool(true));
    let model = SmallModel::from_smt_model(&smt_model);
    assert_eq!(model.int_assignments.get("a"), Some(&10));
    assert_eq!(model.bool_assignments.get("b"), Some(&true));
}

#[test]
fn test_implication_cache_hit() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let cons = ChcExpr::ge(x, ChcExpr::int(-1));
    cache.record_result(&ant, &cons, ImplicationResult::Valid, None);
    assert_eq!(
        cache.check_with_hints(&ant, &cons),
        Some(ImplicationResult::Valid)
    );
    assert_eq!(cache.cache_hits, 1);
}

#[test]
fn test_implication_cache_model_rejection() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let mut countermodel = FxHashMap::default();
    countermodel.insert("x".to_string(), SmtValue::Int(0));
    let cons1 = ChcExpr::gt(x.clone(), ChcExpr::int(0));
    cache.record_result(
        &ant,
        &cons1,
        ImplicationResult::Invalid,
        Some(&countermodel),
    );
    let cons2 = ChcExpr::gt(x.clone(), ChcExpr::int(-1));
    assert_eq!(cache.check_with_hints(&ant, &cons2), None);
    let cons3 = ChcExpr::ge(x, ChcExpr::int(1));
    assert_eq!(
        cache.check_with_hints(&ant, &cons3),
        Some(ImplicationResult::Invalid)
    );
    assert_eq!(cache.model_rejections, 1);
}

#[test]
fn test_implication_cache_clear() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));
    let cons = ChcExpr::ge(x, ChcExpr::int(-1));
    cache.record_result(&ant, &cons, ImplicationResult::Valid, None);
    assert_eq!(cache.result_cache.len(), 1);
    cache.clear();
    assert_eq!(cache.result_cache.len(), 0);
    assert_eq!(cache.implication_countermodels.len(), 0);
    assert_eq!(cache.blocking_countermodels.len(), 0);
}

#[test]
fn test_implication_cache_respects_max_models() {
    // Test with custom max_models limit of 4
    let max = 4;
    let mut cache = ImplicationCache::with_max_models(max);
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));

    // Add more than max models for same antecedent
    for i in 0..=(max + 2) {
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::Int(i as i64));
        let cons = ChcExpr::gt(x.clone(), ChcExpr::int(i as i64));
        cache.record_result(&ant, &cons, ImplicationResult::Invalid, Some(&model));
    }

    // Verify only max models are stored (via stats)
    let stats = cache.stats();
    assert_eq!(
        stats.countermodel_count, max,
        "Expected exactly {} models, got {}",
        max, stats.countermodel_count
    );
}

#[test]
fn test_blocking_cache_respects_max_models() {
    // Test blocking API's model limit
    let max = 4;
    let mut cache = ImplicationCache::with_max_models(max);

    // Add more than max models for same (predicate, level)
    for i in 0..=(max + 2) {
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::Int(i as i64));
        cache.record_blocking_countermodel(0, 1, &model);
    }

    // Verify only max models are stored (via stats)
    let stats = cache.stats();
    assert_eq!(
        stats.countermodel_count, max,
        "Expected exactly {} models, got {}",
        max, stats.countermodel_count
    );
}

#[test]
fn test_blocking_cache_model_rejection() {
    // Test the blocking-specific API (used in PDR push phase)
    let mut cache = ImplicationCache::new();

    // Record a model where x=5
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));
    cache.record_blocking_countermodel(0, 1, &model);

    // Formula x >= 5 should be rejected (satisfied by model where x=5)
    let x = ChcExpr::var(int_var("x"));
    let blocking1 = ChcExpr::ge(x.clone(), ChcExpr::int(5));
    assert!(
        cache.blocking_rejected_by_cache(0, 1, &blocking1),
        "Model x=5 should satisfy x >= 5"
    );

    // Formula x > 5 should NOT be rejected (model x=5 doesn't satisfy x > 5)
    let blocking2 = ChcExpr::gt(x, ChcExpr::int(5));
    assert!(
        !cache.blocking_rejected_by_cache(0, 1, &blocking2),
        "Model x=5 should not satisfy x > 5"
    );

    // Different predicate/level should not be affected
    assert!(
        !cache.blocking_rejected_by_cache(1, 1, &blocking1),
        "Different predicate should have no cached models"
    );
    assert!(
        !cache.blocking_rejected_by_cache(0, 2, &blocking1),
        "Different level should have no cached models"
    );
}

#[test]
fn test_stats_tracking() {
    let mut cache = ImplicationCache::new();
    let x = ChcExpr::var(int_var("x"));
    let ant = ChcExpr::ge(x.clone(), ChcExpr::int(0));

    // Initial stats
    let stats = cache.stats();
    assert_eq!(stats.cache_hits, 0);
    assert_eq!(stats.model_rejections, 0);
    assert_eq!(stats.solver_calls, 0);

    // Record a result with countermodel
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(0));
    let cons = ChcExpr::gt(x.clone(), ChcExpr::int(0));
    cache.record_result(&ant, &cons, ImplicationResult::Invalid, Some(&model));

    let stats = cache.stats();
    assert_eq!(stats.solver_calls, 1);
    assert_eq!(stats.countermodel_count, 1);

    // Check with hints - cache hit
    let _ = cache.check_with_hints(&ant, &cons);
    let stats = cache.stats();
    assert_eq!(stats.cache_hits, 1);

    // New consequent rejected by cached model
    let cons2 = ChcExpr::ge(x, ChcExpr::int(1)); // x=0 doesn't satisfy x >= 1
    let _ = cache.check_with_hints(&ant, &cons2);
    let stats = cache.stats();
    assert_eq!(stats.model_rejections, 1);
}

#[test]
fn test_blocking_key_no_collision() {
    // Test that (predicate=1, level=10000) and (predicate=2, level=0) don't collide.
    // With the old formula (predicate * 10000 + level), both would produce key=20000.
    // Using (predicate_idx, level) as the map key prevents this.
    let mut cache = ImplicationCache::new();

    // Add model for (predicate=1, level=10000)
    let mut model1 = FxHashMap::default();
    model1.insert("x".to_string(), SmtValue::Int(100));
    cache.record_blocking_countermodel(1, 10000, &model1);

    // Add model for (predicate=2, level=0)
    let mut model2 = FxHashMap::default();
    model2.insert("x".to_string(), SmtValue::Int(200));
    cache.record_blocking_countermodel(2, 0, &model2);

    // Verify both models are stored (2 distinct keys)
    let stats = cache.stats();
    assert_eq!(
        stats.countermodel_count, 2,
        "Should have 2 models for 2 distinct keys"
    );

    // Verify (predicate=1, level=10000) only sees model with x=100
    let x = ChcExpr::var(int_var("x"));
    let formula_100 = ChcExpr::eq(x.clone(), ChcExpr::int(100));
    let formula_200 = ChcExpr::eq(x, ChcExpr::int(200));

    assert!(
        cache.blocking_rejected_by_cache(1, 10000, &formula_100),
        "(1, 10000) should see x=100 model"
    );
    assert!(
        !cache.blocking_rejected_by_cache(1, 10000, &formula_200),
        "(1, 10000) should NOT see x=200 model (different key)"
    );

    // Verify (predicate=2, level=0) only sees model with x=200
    assert!(
        !cache.blocking_rejected_by_cache(2, 0, &formula_100),
        "(2, 0) should NOT see x=100 model (different key)"
    );
    assert!(
        cache.blocking_rejected_by_cache(2, 0, &formula_200),
        "(2, 0) should see x=200 model"
    );
}

/// Verify blocking_countermodels accumulation under the eviction cap.
/// With 20×50=1000 keys (under MAX_BLOCKING_COUNTERMODEL_KEYS), all entries
/// should be retained.
///
/// Reference: #2924 finding 2c, #3077 finding 4 (eviction cap added)
#[test]
fn test_blocking_countermodels_unbounded_key_growth() {
    let mut cache = ImplicationCache::new();
    let num_predicates = 20;
    let num_levels = 50;

    // Simulate PDR exploring many predicate×level combinations
    for pred in 0..num_predicates {
        for level in 0..num_levels {
            let mut model = FxHashMap::default();
            model.insert("x".to_string(), SmtValue::Int((pred * 100 + level) as i64));
            cache.record_blocking_countermodel(pred, level, &model);
        }
    }

    let stats = cache.stats();
    // Each (predicate, level) pair stores exactly 1 model → total = P * L
    assert_eq!(
        stats.countermodel_count,
        num_predicates * num_levels,
        "Total models should equal num_predicates * num_levels = {} with no eviction",
        num_predicates * num_levels,
    );

    // Prove there is no production clear/evict mechanism:
    // Add more models — they accumulate, never shrink.
    for pred in 0..num_predicates {
        for level in 0..num_levels {
            let mut model = FxHashMap::default();
            model.insert("y".to_string(), SmtValue::Int(999));
            cache.record_blocking_countermodel(pred, level, &model);
        }
    }

    let stats2 = cache.stats();
    // Now each key has 2 models (max_models_per_key=8, so both fit)
    assert_eq!(
        stats2.countermodel_count,
        num_predicates * num_levels * 2,
        "Under cap: {} keys * 2 models each should all be retained",
        num_predicates * num_levels,
    );
}

/// Verify that blocking_countermodels evicts when key count exceeds cap (#3077).
#[test]
fn test_blocking_countermodels_eviction_at_cap() {
    let mut cache = ImplicationCache::new();

    // Fill to exactly the cap
    for i in 0..MAX_BLOCKING_COUNTERMODEL_KEYS {
        let mut model = FxHashMap::default();
        model.insert("x".to_string(), SmtValue::Int(i as i64));
        cache.record_blocking_countermodel(i, 0, &model);
    }
    assert_eq!(
        cache.blocking_countermodels.len(),
        MAX_BLOCKING_COUNTERMODEL_KEYS,
    );

    // Adding one more distinct key triggers eviction (clear + insert)
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(999_999));
    cache.record_blocking_countermodel(999_999, 0, &model);

    // After eviction: only the newly inserted key remains
    assert_eq!(cache.blocking_countermodels.len(), 1);
    assert!(cache.blocking_countermodels.contains_key(&(999_999, 0)));
}

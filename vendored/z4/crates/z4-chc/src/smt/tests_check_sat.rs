// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for check_sat BV caching and theory dispatch.
//!
//! Extracted from check_sat.rs inline tests.

use super::check_sat::{
    bv_bitblast_count_for_tests, bv_new_clause_count_for_tests, cached_bv_clause_count_for_tests,
    reset_reuse_counters_for_tests,
};
use super::context::SmtContext;
use super::types::SmtResult;
use crate::{ChcExpr, ChcSort, ChcVar};
use serial_test::serial;

#[test]
#[serial]
fn test_check_sat_skips_bv_setup_for_pure_lia_6614() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(1));

    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected pure arithmetic query to be SAT, got {result:?}",
    );
    assert_eq!(
        bv_bitblast_count_for_tests(),
        0,
        "pure arithmetic query should not enter BV bit-blasting setup",
    );
}

#[test]
#[serial]
fn test_check_sat_runs_bv_setup_for_bv_query_6614() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 8));

    let result = ctx.check_sat(&query);

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected BV equality query to be SAT, got {result:?}",
    );
    assert!(
        bv_bitblast_count_for_tests() >= 1,
        "BV query should enter BV bit-blasting setup",
    );
}

#[test]
#[serial]
fn test_check_sat_reuses_bv_clauses_after_reset_5877() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let query = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(x)),
                std::sync::Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
        ChcExpr::BitVec(3, 8),
    );

    let first = ctx.check_sat(&query);
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected first BV query to be SAT, got {first:?}",
    );
    let first_new_clause_count = bv_new_clause_count_for_tests();
    assert!(
        first_new_clause_count > 0,
        "expected first BV query to generate BV clauses",
    );

    ctx.reset();

    let second = ctx.check_sat(&query);
    assert!(
        matches!(second, SmtResult::Sat(_)),
        "expected second BV query to be SAT, got {second:?}",
    );
    let second_new_clause_count = bv_new_clause_count_for_tests();
    assert_eq!(
        second_new_clause_count, first_new_clause_count,
        "expected reset()+same-query BV solve to replay cached BV clauses without new generation",
    );
}

#[test]
#[serial]
fn test_check_sat_does_not_reuse_bv_cache_across_width_change_5877() {
    reset_reuse_counters_for_tests();

    let mut ctx = SmtContext::new();
    let x8 = ChcVar::new("x", ChcSort::BitVec(8));
    let query8 = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(x8)),
                std::sync::Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
        ChcExpr::BitVec(3, 8),
    );
    let first = ctx.check_sat(&query8);
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected 8-bit BV query to be SAT, got {first:?}",
    );
    let first_new_clause_count = bv_new_clause_count_for_tests();
    assert!(
        first_new_clause_count > 0,
        "expected 8-bit BV query to generate BV clauses",
    );

    ctx.reset();

    let x16 = ChcVar::new("x", ChcSort::BitVec(16));
    let query16 = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(x16)),
                std::sync::Arc::new(ChcExpr::BitVec(1, 16)),
            ],
        ),
        ChcExpr::BitVec(3, 16),
    );
    let second = ctx.check_sat(&query16);
    assert!(
        matches!(second, SmtResult::Sat(_)),
        "expected 16-bit BV query to be SAT, got {second:?}",
    );
    let second_new_clause_count = bv_new_clause_count_for_tests();
    assert!(
        second_new_clause_count > first_new_clause_count,
        "expected width change to force new BV clauses instead of reusing 8-bit cache",
    );
}

#[test]
#[serial]
fn test_check_sat_replaces_bv_cache_for_new_query_shape_5877() {
    let query_a = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::BvAdd,
            vec![
                std::sync::Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)))),
                std::sync::Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
        ChcExpr::BitVec(3, 8),
    );
    let query_b = ChcExpr::Op(
        crate::ChcOp::BvSLt,
        vec![
            std::sync::Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)))),
            std::sync::Arc::new(ChcExpr::BitVec(10, 8)),
        ],
    );

    let mut warmed = SmtContext::new();
    let first = warmed.check_sat(&query_a);
    assert!(
        matches!(first, SmtResult::Sat(_)),
        "expected first BV query to be SAT, got {first:?}",
    );
    assert!(
        cached_bv_clause_count_for_tests(&warmed) > 0,
        "expected first BV query to populate persistent BV cache",
    );

    warmed.reset();

    let second = warmed.check_sat(&query_b);
    assert!(
        matches!(second, SmtResult::Sat(_)),
        "expected second BV query to be SAT, got {second:?}",
    );
    let warmed_cache_len = cached_bv_clause_count_for_tests(&warmed);

    let mut fresh = SmtContext::new();
    let fresh_result = fresh.check_sat(&query_b);
    assert!(
        matches!(fresh_result, SmtResult::Sat(_)),
        "expected fresh BV query to be SAT, got {fresh_result:?}",
    );
    let fresh_cache_len = cached_bv_clause_count_for_tests(&fresh);

    assert_eq!(
        warmed_cache_len, fresh_cache_len,
        "expected persistent BV cache to snapshot the latest query shape instead of accumulating prior clauses",
    );
}

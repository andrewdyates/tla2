// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn no_bv_passthrough() {
    let p = ChcProblem::new();
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(r.problem.predicates().len(), 0);
}

#[test]
fn bv8_expanded_to_8_bools() {
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(8), ChcSort::Int]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 8 Bool args + 1 Int arg = 9
    assert_eq!(sorts.len(), 9);
    assert!(sorts[..8].iter().all(|s| *s == ChcSort::Bool));
    assert_eq!(sorts[8], ChcSort::Int);
}

#[test]
fn bv32_expanded_to_32_bools() {
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(32)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(r.problem.predicates()[0].arg_sorts.len(), 32);
    assert!(r.problem.predicates()[0]
        .arg_sorts
        .iter()
        .all(|s| *s == ChcSort::Bool));
}

#[test]
fn bv64_expanded_to_64_bools() {
    // #7975: BV64 is now within the bitblast threshold (64) and should be expanded.
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(64)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(r.problem.predicates()[0].arg_sorts.len(), 64);
    assert!(r.problem.predicates()[0]
        .arg_sorts
        .iter()
        .all(|s| *s == ChcSort::Bool));
}

#[test]
fn bv128_only_passthrough() {
    // When ALL BV args exceed the threshold (64), the transformer should skip entirely.
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(128)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    assert_eq!(
        r.problem.predicates()[0].arg_sorts,
        vec![ChcSort::BitVec(128)]
    );
}

#[test]
fn mixed_bv8_bv64_all_bitblasted() {
    // #7975: Both BV8 and BV64 are within the threshold (64) — both bit-blasted.
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![ChcSort::BitVec(8), ChcSort::BitVec(64), ChcSort::Int],
    );
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 8 Bools (from BV8) + 64 Bools (from BV64) + 1 Int = 73
    assert_eq!(sorts.len(), 73);
    assert!(sorts[..8].iter().all(|s| *s == ChcSort::Bool));
    assert!(sorts[8..72].iter().all(|s| *s == ChcSort::Bool));
    assert_eq!(sorts[72], ChcSort::Int);
}

#[test]
fn mixed_bv32_bv64_all_bitblasted() {
    // #7975: Both BV32 and BV64 are within the threshold — both bit-blasted.
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(32), ChcSort::BitVec(64)]);
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 32 Bools (from BV32) + 64 Bools (from BV64) = 96
    assert_eq!(sorts.len(), 96);
    assert!(sorts.iter().all(|s| *s == ChcSort::Bool));
}

#[test]
fn selective_bitblast_bv8_bv128_mixed() {
    // #7975: BV8 is bitblasted, BV128 exceeds threshold and is preserved.
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![
            ChcSort::BitVec(128),
            ChcSort::BitVec(8),
            ChcSort::BitVec(128),
        ],
    );
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 1 BitVec(128) + 8 Bools + 1 BitVec(128) = 10
    assert_eq!(sorts.len(), 10);
    assert_eq!(sorts[0], ChcSort::BitVec(128));
    assert!(sorts[1..9].iter().all(|s| *s == ChcSort::Bool));
    assert_eq!(sorts[9], ChcSort::BitVec(128));
}

#[test]
fn multiple_bv64_all_bitblasted() {
    // #7975: Multiple BV64 args should all be bit-blasted now.
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![ChcSort::BitVec(64), ChcSort::BitVec(8), ChcSort::BitVec(64)],
    );
    let r = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    // 64 Bools + 8 Bools + 64 Bools = 136
    assert_eq!(sorts.len(), 136);
    assert!(sorts.iter().all(|s| *s == ChcSort::Bool));
}

#[test]
fn back_translation_restores_bv_sorts() {
    let mut map = BvBoolMap::new();
    let pid = PredicateId::new(0);
    map.pred_original_sorts
        .insert(pid, vec![ChcSort::BitVec(8), ChcSort::Int]);
    map.pred_arg_bitblasted.insert(pid, vec![true, false]);

    let mut inv = InvariantModel::new();
    let mut vars = Vec::new();
    for i in 0..8 {
        vars.push(ChcVar::new(format!("x0_b{i}"), ChcSort::Bool));
    }
    vars.push(ChcVar::new("x1", ChcSort::Int));
    inv.set(pid, PredicateInterpretation::new(vars, ChcExpr::Bool(true)));

    let result = reconstruct_bv_invariant(&inv, &map);
    let interp = result.get(&pid).unwrap();
    // Should have 2 vars: one BV(8) and one Int
    assert_eq!(interp.vars.len(), 2);
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(8));
    assert_eq!(interp.vars[1].sort, ChcSort::Int);
}

#[test]
fn back_translation_selective_mixed_bv8_bv64() {
    // #7006/#7019: Back-translation with mixed bit-blasted and non-bit-blasted args.
    let mut map = BvBoolMap::new();
    let pid = PredicateId::new(0);
    map.pred_original_sorts.insert(
        pid,
        vec![ChcSort::BitVec(8), ChcSort::BitVec(64), ChcSort::Int],
    );
    // BV8 was bit-blasted, BV64 was not, Int was not.
    map.pred_arg_bitblasted
        .insert(pid, vec![true, false, false]);

    let mut inv = InvariantModel::new();
    let mut vars = Vec::new();
    // 8 Bool vars for the bit-blasted BV8
    for i in 0..8 {
        vars.push(ChcVar::new(format!("x0_b{i}"), ChcSort::Bool));
    }
    // 1 BV64 var (not bit-blasted, passed through)
    vars.push(ChcVar::new("x1", ChcSort::BitVec(64)));
    // 1 Int var
    vars.push(ChcVar::new("x2", ChcSort::Int));
    inv.set(pid, PredicateInterpretation::new(vars, ChcExpr::Bool(true)));

    let result = reconstruct_bv_invariant(&inv, &map);
    let interp = result.get(&pid).unwrap();
    // Should have 3 vars: BV(8), BV(64), Int
    assert_eq!(interp.vars.len(), 3);
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(8));
    assert_eq!(interp.vars[1].sort, ChcSort::BitVec(64));
    assert_eq!(interp.vars[2].sort, ChcSort::Int);
}

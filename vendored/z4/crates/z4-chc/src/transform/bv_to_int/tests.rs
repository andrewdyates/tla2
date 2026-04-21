// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;
use crate::pdr::counterexample::{Counterexample, DerivationWitness, DerivationWitnessEntry};
use crate::smt::SmtValue;
use crate::transform::BvToBoolBitBlaster;
use crate::ChcOp;
use rustc_hash::FxHashMap;

/// Create a minimal CHC problem with a single BV predicate of the given width.
fn make_simple_bv_problem(width: u32) -> ChcProblem {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(width)]);
    let x = ChcVar::new("x", ChcSort::BitVec(width));
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));
    p
}

fn expr_contains_op(expr: &ChcExpr, target: &ChcOp) -> bool {
    match expr {
        ChcExpr::Op(op, args) => {
            op == target
                || args
                    .iter()
                    .any(|arg| expr_contains_op(arg.as_ref(), target))
        }
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => args
            .iter()
            .any(|arg| expr_contains_op(arg.as_ref(), target)),
        ChcExpr::ConstArray(_, value) => expr_contains_op(value.as_ref(), target),
        _ => false,
    }
}

#[test]
fn no_bv_passthrough() {
    let p = ChcProblem::new();
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert_eq!(r.problem.predicates().len(), 0);
}

#[test]
fn bv_sort_replacement() {
    let mut p = ChcProblem::new();
    p.declare_predicate("inv", vec![ChcSort::BitVec(32), ChcSort::Int]);
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert_eq!(
        r.problem.predicates()[0].arg_sorts,
        vec![ChcSort::Int, ChcSort::Int]
    );
}

#[test]
fn bvadd_exact_encoding() {
    let mut map = BvIntMap::new();
    let add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8)))),
        ],
    );
    let result = abstract_expr(&add, &mut map, false);
    assert!(matches!(result, ChcExpr::Op(ChcOp::Ite, _)));
}

#[test]
fn bv_constant_to_int() {
    let mut map = BvIntMap::new();
    assert!(matches!(
        abstract_expr(&ChcExpr::BitVec(42, 32), &mut map, false),
        ChcExpr::Int(42)
    ));
}

#[test]
fn unsigned_compare_exact() {
    let mut map = BvIntMap::new();
    let ult = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(32)))),
        ],
    );
    assert!(matches!(
        abstract_expr(&ult, &mut map, false),
        ChcExpr::Op(ChcOp::Lt, _)
    ));
}

#[test]
fn bvult_bv64_normalizes_operands_7006() {
    let mut map = BvIntMap::new();
    let ult = ChcExpr::Op(
        ChcOp::BvULt,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    let result = abstract_expr(&ult, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mod, _)));
            assert!(matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::Mod, _)));
        }
        other => panic!("BV64 ult should normalize both operands, got: {other}"),
    }
}

#[test]
fn bvcomp_bv64_normalizes_operands_7006() {
    let mut map = BvIntMap::new();
    let comp = ChcExpr::Op(
        ChcOp::BvComp,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    let result = abstract_expr(&comp, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Ite, ref args) if args.len() == 3 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _)));
            assert!(
                expr_contains_op(&result, &ChcOp::Mod),
                "bvcomp should normalize wide operands before equality, got: {result}"
            );
        }
        other => panic!("BV64 comp should normalize both operands, got: {other}"),
    }
}

#[test]
fn bitwise_over_approximated() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(32)))),
        ],
    );
    match abstract_expr(&bvand, &mut map, false) {
        ChcExpr::FuncApp(n, ChcSort::Int, a) => {
            assert!(n.starts_with("__bv2int_"));
            assert_eq!(a.len(), 2);
        }
        other => panic!("Expected FuncApp, got: {other}"),
    }
}

#[test]
fn range_constraints_added() {
    let mut p = ChcProblem::new();
    let inv = p.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    p.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    assert!(r.problem.predicates()[0]
        .arg_sorts
        .iter()
        .all(|s| *s == ChcSort::Int));
}

#[test]
fn bv_array_subsort_abstraction() {
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![
            ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
            ChcSort::BitVec(32),
        ],
    );
    let r = Box::new(BvToIntAbstractor::new()).transform(p);
    let sorts = &r.problem.predicates()[0].arg_sorts;
    assert_eq!(
        sorts[0],
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
        "Array sub-sort BV(32) should be abstracted to Int"
    );
    assert_eq!(sorts[1], ChcSort::Int);
}

#[test]
fn bv_array_subsort_abstraction_after_bv_to_bool_handoff() {
    let mut p = ChcProblem::new();
    p.declare_predicate(
        "inv",
        vec![
            ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
            ChcSort::BitVec(8),
        ],
    );

    let bit_blasted = Box::new(BvToBoolBitBlaster::new()).transform(p);
    let blasted_sorts = &bit_blasted.problem.predicates()[0].arg_sorts;
    assert_eq!(
        blasted_sorts[0],
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
        "BvToBool should leave Array(BV, _) arguments for the Int fallback"
    );
    assert!(
        blasted_sorts[1..].iter().all(|sort| *sort == ChcSort::Bool),
        "direct BV argument should expand to Bool bits before the Int fallback"
    );

    let abstracted = Box::new(BvToIntAbstractor::new()).transform(bit_blasted.problem);
    let abstracted_sorts = &abstracted.problem.predicates()[0].arg_sorts;
    assert_eq!(
        abstracted_sorts[0],
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
        "BvToInt must still abstract recursive BV sub-sorts after BvToBool"
    );
    assert!(
        abstracted_sorts[1..]
            .iter()
            .all(|sort| *sort == ChcSort::Bool),
        "BvToInt should preserve the Bool bits produced by BvToBool"
    );
}

#[test]
fn const_array_key_sort_abstracted() {
    let mut map = BvIntMap::new();
    let const_arr = ChcExpr::ConstArray(ChcSort::BitVec(32), Arc::new(ChcExpr::Bool(false)));
    let result = abstract_expr(&const_arr, &mut map, false);
    match &result {
        ChcExpr::ConstArray(ks, _) => {
            assert_eq!(
                *ks,
                ChcSort::Int,
                "ConstArray key sort BV(32) should be abstracted to Int"
            );
        }
        other => panic!("Expected ConstArray, got: {other}"),
    }
}

#[test]
fn var_array_bv_sort_abstracted() {
    let mut map = BvIntMap::new();
    let var = ChcExpr::Var(ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::Int)),
    ));
    let result = abstract_expr(&var, &mut map, false);
    match &result {
        ChcExpr::Var(v) => {
            assert_eq!(
                v.sort,
                ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
                "Var with Array(BV(8), Int) should become Array(Int, Int)"
            );
        }
        other => panic!("Expected Var, got: {other}"),
    }
}

#[test]
fn bvmul_exact_encoding() {
    let mut map = BvIntMap::new();
    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))));
    let y = Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(8))));
    let result = abstract_expr(&ChcExpr::Op(ChcOp::BvMul, vec![x, y]), &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "got: {result}"
    );
}

#[test]
fn back_translation_restores_bv_sorts() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths
        .insert(pid, vec![Some(32), None, Some(8)]);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![
                ChcVar::new("x", ChcSort::Int),
                ChcVar::new("y", ChcSort::Int),
                ChcVar::new("z", ChcSort::Int),
            ],
            ChcExpr::Bool(true),
        ),
    );
    let r = concretize_inv(&inv, &map);
    let interp = r.get(&pid).unwrap();
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(interp.vars[1].sort, ChcSort::Int);
    assert_eq!(interp.vars[2].sort, ChcSort::BitVec(8));
}

#[test]
fn back_translation_rewrites_sorts_by_full_var_identity_not_name() {
    fn has_select_on_array_named_dup(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Select, args)
                if args.len() == 2
                    && matches!(
                        args[0].as_ref(),
                        ChcExpr::Var(v)
                            if v.name == "dup"
                                && v.sort
                                    == ChcSort::Array(
                                        Box::new(ChcSort::Int),
                                        Box::new(ChcSort::Int)
                                    )
                    ) =>
            {
                true
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                args.iter().any(|arg| has_select_on_array_named_dup(arg))
            }
            ChcExpr::ConstArray(_, value) => has_select_on_array_named_dup(value),
            _ => false,
        }
    }

    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);
    map.pred_arg_sorts.insert(pid, vec![ChcSort::BitVec(32)]);

    let scalar_dup = ChcVar::new("dup", ChcSort::Int);
    let array_dup = ChcVar::new(
        "dup",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let formula = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(scalar_dup.clone()), ChcExpr::int(4)),
        ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(array_dup), ChcExpr::int(1)),
            ChcExpr::int(4),
        ),
    );

    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(vec![scalar_dup.clone()], formula),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(
        interp.vars[0].sort,
        ChcSort::BitVec(32),
        "predicate parameter should still concretize back to BV32"
    );
    assert!(
        has_select_on_array_named_dup(&interp.formula),
        "array-valued local with the same name as a BV parameter must stay array-sorted: {}",
        interp.formula
    );
}

#[test]
fn invalidity_back_translation_concretizes_bitvec_instances_6293() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let transformed = Box::new(BvToIntAbstractor::new()).transform(problem);

    let canonical_name = format!("__p{}_a0", pred.index());
    let mut instances = FxHashMap::default();
    instances.insert(canonical_name.clone(), SmtValue::Int(257));

    let cex = Counterexample::with_witness(
        Vec::new(),
        DerivationWitness {
            query_clause: None,
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::Bool(true),
                incoming_clause: None,
                premises: Vec::new(),
                instances,
            }],
        },
    );

    let translated = transformed.back_translator.translate_invalidity(cex);
    let witness = translated
        .witness
        .expect("translated counterexample should keep witness");
    assert_eq!(
        witness.entries[0].instances.get(&canonical_name),
        Some(&SmtValue::BitVec(1, 8))
    );
}

#[test]
fn invalidity_back_translation_concretizes_array_bv_instances_6293() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate(
        "inv",
        vec![ChcSort::Array(
            Box::new(ChcSort::BitVec(8)),
            Box::new(ChcSort::BitVec(16)),
        )],
    );
    let transformed = Box::new(BvToIntAbstractor::new()).transform(problem);

    let canonical_name = format!("__p{}_a0", pred.index());
    let mut instances = FxHashMap::default();
    instances.insert(
        canonical_name.clone(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(258)),
            entries: vec![(SmtValue::Int(-1), SmtValue::Int(513))],
        },
    );

    let cex = Counterexample::with_witness(
        Vec::new(),
        DerivationWitness {
            query_clause: None,
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::Bool(true),
                incoming_clause: None,
                premises: Vec::new(),
                instances,
            }],
        },
    );

    let translated = transformed.back_translator.translate_invalidity(cex);
    let witness = translated
        .witness
        .expect("translated counterexample should keep witness");
    assert_eq!(
        witness.entries[0].instances.get(&canonical_name),
        Some(&SmtValue::ArrayMap {
            default: Box::new(SmtValue::BitVec(258, 16)),
            entries: vec![(SmtValue::BitVec(255, 8), SmtValue::BitVec(513, 16))],
        })
    );
}

/// Back-translation must transform Int constants in formulas to BV constants.
/// Specifically, `select(v, 0)` where v has sort `Array(BV32, Bool)` must become
/// `select(v, (_ bv0 32))` after concretization. Without this, the formula
/// fails sort-checking during verification against the original BV problem.
#[test]
fn back_translation_transforms_formula_int_to_bv_7006() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    // Original predicate has: BV32 counter, Array(BV32, Bool)
    let orig_sorts = vec![
        ChcSort::BitVec(32),
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
    ];
    map.pred_arg_widths.insert(pid, vec![Some(32), None]);
    map.pred_arg_sorts.insert(pid, orig_sorts);
    // Build an Int-domain invariant: `select(v1, 0) = true`
    // This is what the solver produces: array has Int key sort, Int index constant.
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v1 = ChcVar::new(
        "v1",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool)),
    );
    let select_int = ChcExpr::select(ChcExpr::var(v1.clone()), ChcExpr::int(0));
    let formula = ChcExpr::eq(select_int, ChcExpr::Bool(true));
    let mut inv = InvariantModel::new();
    inv.set(pid, PredicateInterpretation::new(vec![v0, v1], formula));
    let r = concretize_inv(&inv, &map);
    let interp = r.get(&pid).unwrap();
    // v0 should become BV32-sorted
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    // v1 should be restored to Array(BV32, Bool) from original sorts
    assert_eq!(
        interp.vars[1].sort,
        ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool)),
        "Array variable sort should be restored from pred_arg_sorts"
    );
    // The formula should have Int 0 converted to BV 0 in the select index
    let formula_str = format!("{}", interp.formula);
    assert!(
        !formula_str.contains("(select v1 0)"),
        "Int constant 0 should be converted to BV in select index, got: {formula_str}"
    );
}

#[test]
fn back_translation_simplifies_out_of_range_bv_upper_bound_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(4_294_967_296)),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(true),
        "x < 2^32 must stay tautological after BV32 back-translation"
    );
}

#[test]
fn back_translation_rejects_out_of_range_bv_equality_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(4_294_967_296)),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(false),
        "x = 2^32 must become false for BV32 back-translation"
    );
}

#[test]
fn back_translation_handles_reversed_out_of_range_bv_comparison_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::gt(ChcExpr::int(4_294_967_296), ChcExpr::var(x)),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(true),
        "2^32 > x must stay tautological for BV32 back-translation"
    );
}

#[test]
fn back_translation_simplifies_unsigned_range_guards_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![None, Some(32)]);
    map.pred_arg_sorts
        .insert(pid, vec![ChcSort::Bool, ChcSort::BitVec(32)]);

    let keep = ChcVar::new("keep", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(
            vec![keep.clone(), x.clone()],
            ChcExpr::and_all(vec![
                ChcExpr::var(keep.clone()),
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(4_294_967_296)),
            ]),
        ),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::Bool);
    assert_eq!(interp.vars[1].sort, ChcSort::BitVec(32));
    assert_eq!(
        interp.formula,
        ChcExpr::var(keep),
        "Unsigned BV range guards must simplify away during back-translation"
    );
}

#[test]
fn back_translation_preserves_wrap_guard_ite_in_int_domain_5877() {
    let mut map = BvIntMap::new();
    let pid = PredicateId::new(0);
    map.pred_arg_widths.insert(pid, vec![Some(32)]);
    map.pred_arg_sorts.insert(pid, vec![ChcSort::BitVec(32)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let sum = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1));
    let wrap_guard = ChcExpr::lt(sum.clone(), ChcExpr::int(4_294_967_296));
    let wrapped = ChcExpr::sub(sum.clone(), ChcExpr::int(4_294_967_296));
    let mut inv = InvariantModel::new();
    inv.set(
        pid,
        PredicateInterpretation::new(vec![x], ChcExpr::ite(wrap_guard, sum, wrapped)),
    );

    let translated = concretize_inv(&inv, &map);
    let interp = translated.get(&pid).expect("predicate should be present");
    assert_eq!(interp.vars[0].sort, ChcSort::BitVec(32));
    let lifted_sum = ChcExpr::add(
        ChcExpr::Op(
            ChcOp::Bv2Nat,
            vec![Arc::new(ChcExpr::var(ChcVar::new(
                "x",
                ChcSort::BitVec(32),
            )))],
        ),
        ChcExpr::int(1),
    );
    assert_eq!(
        interp.formula,
        ChcExpr::ite(
            ChcExpr::lt(lifted_sum.clone(), ChcExpr::int(4_294_967_296)),
            lifted_sum.clone(),
            ChcExpr::sub(lifted_sum, ChcExpr::int(4_294_967_296)),
        ),
        "Back-translation should preserve the learned Int-domain wrap guard"
    );
}

/// `coerce_to_sort` must handle negative Int values with proper modular arithmetic.
#[test]
fn coerce_negative_int_to_bv() {
    // -1 mod 2^8 = 255
    let result = coerce_to_sort(&ChcExpr::Int(-1), &ChcSort::BitVec(8));
    assert_eq!(result, ChcExpr::BitVec(255, 8));

    // -256 mod 2^8 = 0
    let result = coerce_to_sort(&ChcExpr::Int(-256), &ChcSort::BitVec(8));
    assert_eq!(result, ChcExpr::BitVec(0, 8));

    // 0 mod 2^32 = 0
    let result = coerce_to_sort(&ChcExpr::Int(0), &ChcSort::BitVec(32));
    assert_eq!(result, ChcExpr::BitVec(0, 32));

    // 42 mod 2^32 = 42
    let result = coerce_to_sort(&ChcExpr::Int(42), &ChcSort::BitVec(32));
    assert_eq!(result, ChcExpr::BitVec(42, 32));
}

/// `int_cmp_to_bv` maps Int comparisons to unsigned BV comparisons.
#[test]
fn int_cmp_to_bv_mapping() {
    assert_eq!(int_cmp_to_bv(&ChcOp::Eq), ChcOp::Eq);
    assert_eq!(int_cmp_to_bv(&ChcOp::Ne), ChcOp::Ne);
    assert_eq!(int_cmp_to_bv(&ChcOp::Lt), ChcOp::BvULt);
    assert_eq!(int_cmp_to_bv(&ChcOp::Le), ChcOp::BvULe);
    assert_eq!(int_cmp_to_bv(&ChcOp::Gt), ChcOp::BvUGt);
    assert_eq!(int_cmp_to_bv(&ChcOp::Ge), ChcOp::BvUGe);
}

#[test]
fn backtranslate_bv_arithmetic_preserves_int_semantics() {
    let sort_env = FxHashMap::from_iter([(ChcVar::new("x", ChcSort::Int), ChcSort::BitVec(32))]);
    let abstract_formula = ChcExpr::lt(
        ChcExpr::add(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(1),
        ),
        ChcExpr::int(5),
    );

    let translated = int_to_bv_formula(&abstract_formula, &sort_env);
    let expected = ChcExpr::lt(
        ChcExpr::add(
            ChcExpr::Op(
                ChcOp::Bv2Nat,
                vec![Arc::new(ChcExpr::var(ChcVar::new(
                    "x",
                    ChcSort::BitVec(32),
                )))],
            ),
            ChcExpr::int(1),
        ),
        ChcExpr::int(5),
    );

    assert_eq!(
        translated, expected,
        "back-translation must preserve learned Int arithmetic over BV vars"
    );
}

#[test]
fn backtranslate_bv_comparison_uses_bv2nat_when_not_constant_foldable() {
    let sort_env = FxHashMap::from_iter([
        (ChcVar::new("x", ChcSort::Int), ChcSort::BitVec(32)),
        (ChcVar::new("y", ChcSort::Int), ChcSort::BitVec(32)),
    ]);
    let abstract_formula = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
    );

    let translated = int_to_bv_formula(&abstract_formula, &sort_env);
    let expected = ChcExpr::ge(
        ChcExpr::Op(
            ChcOp::Bv2Nat,
            vec![Arc::new(ChcExpr::var(ChcVar::new(
                "x",
                ChcSort::BitVec(32),
            )))],
        ),
        ChcExpr::Op(
            ChcOp::Bv2Nat,
            vec![Arc::new(ChcExpr::var(ChcVar::new(
                "y",
                ChcSort::BitVec(32),
            )))],
        ),
    );

    assert_eq!(
        translated, expected,
        "non-foldable BV comparisons must remain Int comparisons over bv2nat"
    );
}

/// Mixed Int+BV predicate: Int arguments must be preserved after concretization.
/// This catches the bug where a predicate-wide `has_bv_args` audit would
/// incorrectly reject legitimate Int witness values in mixed-signature predicates
/// like `(Int, BitVec(8))`.
#[test]
fn invalidity_back_translation_preserves_non_bv_instances_in_mixed_signature_6293() {
    let mut problem = ChcProblem::new();
    // Mixed signature: first arg is Int, second is BitVec(8)
    let pred = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::BitVec(8)]);
    let transformed = Box::new(BvToIntAbstractor::new()).transform(problem);

    let int_canonical = format!("__p{}_a0", pred.index());
    let bv_canonical = format!("__p{}_a1", pred.index());
    let mut instances = FxHashMap::default();
    instances.insert(int_canonical.clone(), SmtValue::Int(42));
    instances.insert(bv_canonical.clone(), SmtValue::Int(300));

    let cex = Counterexample::with_witness(
        Vec::new(),
        DerivationWitness {
            query_clause: None,
            root: 0,
            entries: vec![DerivationWitnessEntry {
                predicate: pred,
                level: 0,
                state: ChcExpr::Bool(true),
                incoming_clause: None,
                premises: Vec::new(),
                instances,
            }],
        },
    );

    let translated = transformed.back_translator.translate_invalidity(cex);
    let witness = translated
        .witness
        .expect("translated counterexample should keep witness");

    // Int argument must be preserved unchanged
    assert_eq!(
        witness.entries[0].instances.get(&int_canonical),
        Some(&SmtValue::Int(42)),
        "Int argument in mixed-signature predicate must remain Int"
    );
    // BV argument must be concretized: 300 mod 256 = 44
    assert_eq!(
        witness.entries[0].instances.get(&bv_canonical),
        Some(&SmtValue::BitVec(44, 8)),
        "BV argument in mixed-signature predicate must be concretized"
    );
}

#[test]
fn bvadd_relaxed_uses_plain_integer_addition() {
    let mut map = BvIntMap::new();
    let x_bv = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let y_bv = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(8)));
    let add = ChcExpr::Op(ChcOp::BvAdd, vec![Arc::new(x_bv), Arc::new(y_bv)]);
    let x_int = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y_int = ChcExpr::var(ChcVar::new("y", ChcSort::Int));

    let result = abstract_expr(&add, &mut map, true);

    assert_eq!(
        result,
        ChcExpr::add(x_int, y_int),
        "relaxed BV add must skip modular ITE wrapping"
    );
}

#[test]
fn bvudiv_relaxed_guards_zero_divisor() {
    let mut map = BvIntMap::new();
    let x_bv = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(16)));
    let y_bv = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(16)));
    let div = ChcExpr::Op(ChcOp::BvUDiv, vec![Arc::new(x_bv), Arc::new(y_bv)]);
    let x_int = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y_int = ChcExpr::var(ChcVar::new("y", ChcSort::Int));

    let result = abstract_expr(&div, &mut map, true);

    assert_eq!(
        result,
        ChcExpr::ite(
            ChcExpr::eq(y_int.clone(), ChcExpr::int(0)),
            ChcExpr::int(0),
            ChcExpr::Op(ChcOp::Div, vec![Arc::new(x_int), Arc::new(y_int)]),
        ),
        "relaxed BV udiv must guard divide-by-zero explicitly"
    );
}

#[test]
fn bvudiv_bv64_normalizes_operands_7006() {
    let mut map = BvIntMap::new();
    let div = ChcExpr::Op(
        ChcOp::BvUDiv,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::BitVec(64)))),
        ],
    );
    let result = abstract_expr(&div, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _)));
            assert!(matches!(args[2].as_ref(), ChcExpr::Op(ChcOp::Div, _)));
        }
        other => panic!("BV64 udiv should normalize both operands, got: {other}"),
    }
}

#[test]
fn bvslt_relaxed_uses_plain_integer_order() {
    let mut map = BvIntMap::new();
    let x_bv = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)));
    let y_bv = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(8)));
    let slt = ChcExpr::Op(ChcOp::BvSLt, vec![Arc::new(x_bv), Arc::new(y_bv)]);
    let x_int = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y_int = ChcExpr::var(ChcVar::new("y", ChcSort::Int));

    let result = abstract_expr(&slt, &mut map, true);

    assert_eq!(
        result,
        ChcExpr::lt(x_int, y_int),
        "relaxed signed compare must over-approximate with plain integer order"
    );
}

#[test]
fn bvneg_bv64_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let neg = ChcExpr::Op(
        ChcOp::BvNeg,
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&neg, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _)));
            assert!(matches!(args[2].as_ref(), ChcExpr::Op(ChcOp::Sub, _)));
        }
        other => panic!("BV64 neg should normalize the operand, got: {other}"),
    }
}

#[test]
fn bv2nat_bv64_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let bv2nat = ChcExpr::Op(
        ChcOp::Bv2Nat,
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&bv2nat, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "bv2nat on BV64 should normalize via mod 2^64, got: {result}"
    );
}

#[test]
fn relaxed_transform_skips_range_constraints() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let exact = Box::new(BvToIntAbstractor::new()).transform(problem.clone());
    let relaxed = Box::new(BvToIntAbstractor::relaxed()).transform(problem);

    assert!(
        exact.problem.clauses()[0].body.constraint.is_some(),
        "exact BV-to-Int should add head-argument range constraints"
    );
    assert!(
        relaxed.problem.clauses()[0].body.constraint.is_none(),
        "relaxed BV-to-Int must skip range constraints"
    );
}

/// BvConcat with non-BitVec second argument must not panic (#7078).
/// When an upstream transform produces a BvConcat node whose child has Int
/// sort, abstract_op falls back to UF encoding instead of crashing.
#[test]
fn bvconcat_non_bitvec_arg_does_not_panic_7078() {
    let mut map = BvIntMap::new();
    // BvConcat where second argument is Int-sorted (the crash scenario)
    let concat = ChcExpr::Op(
        ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8)))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::Int))),
        ],
    );
    // Exact mode: should produce UF fallback, not panic
    let result = abstract_expr(&concat, &mut map, false);
    assert!(
        matches!(result, ChcExpr::FuncApp(_, ChcSort::Int, _)),
        "BvConcat with Int arg should fall back to UF, got: {result}"
    );
    // Relaxed mode: same UF fallback
    let result_relaxed = abstract_expr(&concat, &mut map, true);
    assert!(
        matches!(result_relaxed, ChcExpr::FuncApp(_, ChcSort::Int, _)),
        "Relaxed BvConcat with Int arg should fall back to UF, got: {result_relaxed}"
    );
}

/// BvAdd with non-BitVec args must not panic (#7078).
/// Tests the early guard for arithmetic BV ops.
#[test]
fn bvadd_non_bitvec_args_does_not_panic_7078() {
    let mut map = BvIntMap::new();
    let add = ChcExpr::Op(
        ChcOp::BvAdd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::Int))),
            Arc::new(ChcExpr::Var(ChcVar::new("y", ChcSort::Int))),
        ],
    );
    let result = abstract_expr(&add, &mut map, false);
    assert!(
        matches!(result, ChcExpr::FuncApp(_, ChcSort::Int, _)),
        "BvAdd with Int args should fall back to UF, got: {result}"
    );
}
#[test]
fn test_int_pow2_small_widths() {
    use super::ops::int_pow2;
    assert_eq!(int_pow2(0), ChcExpr::int(1));
    assert_eq!(int_pow2(1), ChcExpr::int(2));
    assert_eq!(int_pow2(8), ChcExpr::int(256));
    assert_eq!(int_pow2(31), ChcExpr::int(1i64 << 31));
    assert_eq!(int_pow2(32), ChcExpr::int(1i64 << 32));
    assert_eq!(int_pow2(62), ChcExpr::int(1i64 << 62));
}

#[test]
fn test_int_pow2_large_widths() {
    use super::ops::int_pow2;
    // 2^63 = 2^32 * 2^31 (doesn't fit in i64, must be expression)
    let p63 = int_pow2(63);
    assert!(
        matches!(p63, ChcExpr::Op(ChcOp::Mul, _)),
        "2^63 should be Mul expr"
    );

    // 2^64 = 2^32 * 2^32 (doesn't fit in i64, must be expression)
    let p64 = int_pow2(64);
    assert!(
        matches!(p64, ChcExpr::Op(ChcOp::Mul, _)),
        "2^64 should be Mul expr"
    );

    // Verify structure: 2^64 = 2^32 * 2^32
    if let ChcExpr::Op(ChcOp::Mul, ref args) = p64 {
        assert_eq!(*args[0], ChcExpr::int(1i64 << 32));
        assert_eq!(*args[1], ChcExpr::int(1i64 << 32));
    }

    // 2^128 should also work (recursive decomposition)
    let p128 = int_pow2(128);
    assert!(
        matches!(p128, ChcExpr::Op(ChcOp::Mul, _)),
        "2^128 should be Mul expr"
    );
}

/// BvAnd with constant low-bit mask encodes as mod (#7006).
#[test]
fn bvand_const_mask_encodes_as_mod_7006() {
    let mut map = BvIntMap::new();
    // x & 0xFF (8-bit mask on BV32) → x mod 256
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0xFF, 32)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    // Should be mod(x, 256), not UF
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x & 0xFF should encode as x mod 256, got: {result}"
    );
}

/// BvAnd with zero mask → 0 (#7006).
#[test]
fn bvand_zero_mask_returns_zero_7006() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0, 32)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    assert_eq!(result, ChcExpr::int(0), "x & 0 should be 0");
}

/// BvShl with constant shift encodes as mul+mod (#7006).
#[test]
fn bvshl_const_shift_encodes_as_mul_mod_7006() {
    let mut map = BvIntMap::new();
    // x << 4 on BV32 → (x * 16) mod 2^32
    let shl = ChcExpr::Op(
        ChcOp::BvShl,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(4, 32)),
        ],
    );
    let result = abstract_expr(&shl, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x << 4 should encode as mod(x*16, 2^32), got: {result}"
    );
}

/// BvLShr with constant shift encodes as integer division (#7006).
#[test]
fn bvlshr_const_shift_encodes_as_div_7006() {
    let mut map = BvIntMap::new();
    // x >> 3 on BV32 → x / 8
    let lshr = ChcExpr::Op(
        ChcOp::BvLShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(3, 32)),
        ],
    );
    let result = abstract_expr(&lshr, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Div, _)),
        "x >> 3 should encode as x / 8, got: {result}"
    );
}

/// BV64 shifts with expression-shaped constants must stay precise (#7006).
#[test]
fn bvshl_bv64_large_const_shift_returns_zero_7006() {
    let mut map = BvIntMap::new();
    let shl = ChcExpr::Op(
        ChcOp::BvShl,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&shl, &mut map, false);
    assert_eq!(
        result,
        ChcExpr::int(0),
        "x << 0xffff...ffff should encode as 0, got: {result}"
    );
}

/// BV64 logical right shifts with expression-shaped constants must stay precise (#7006).
#[test]
fn bvlshr_bv64_large_const_shift_returns_zero_7006() {
    let mut map = BvIntMap::new();
    let lshr = ChcExpr::Op(
        ChcOp::BvLShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&lshr, &mut map, false);
    assert_eq!(
        result,
        ChcExpr::int(0),
        "x >> 0xffff...ffff should encode as 0, got: {result}"
    );
}

/// BV64 low-slice extracts should lower to a low-bit modulus pattern (#7006).
#[test]
fn bvextract_bv64_low_slice_encodes_as_mod_7006() {
    let mut map = BvIntMap::new();
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(2, 0),
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&extract, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "((_ extract 2 0) x) should encode as a low-bit mod pattern, got: {result}"
    );
}

/// BV64 top-slice extracts should lower to division by the dropped low bits (#7006).
#[test]
fn bvextract_bv64_top_slice_encodes_as_div_7006() {
    let mut map = BvIntMap::new();
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(63, 3),
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&extract, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Div, _)),
        "((_ extract 63 3) x) should encode as division by 8, got: {result}"
    );
}

/// BvNot encodes as 2^w - 1 - x (#7006).
#[test]
fn bvnot_encodes_as_complement_7006() {
    let mut map = BvIntMap::new();
    let not = ChcExpr::Op(
        ChcOp::BvNot,
        vec![Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))))],
    );
    let result = abstract_expr(&not, &mut map, false);
    // Should be 2^8 - 1 - x = 256 - 1 - x
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Sub, _)),
        "~x should encode as (2^w - 1) - x, got: {result}"
    );
}

/// BvOr with zero constant is identity (#7006).
#[test]
fn bvor_zero_is_identity_7006() {
    let mut map = BvIntMap::new();
    let or = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32)))),
            Arc::new(ChcExpr::BitVec(0, 32)),
        ],
    );
    let result = abstract_expr(&or, &mut map, false);
    // Should be just x (identity)
    assert!(
        matches!(result, ChcExpr::Var(_)),
        "x | 0 should be identity, got: {result}"
    );
}

/// BV64 alignment masks like `x & ~7` must stay precise (#7006).
#[test]
fn bvand_bv64_alignment_mask_clears_low_bits_7006() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::Op(
                ChcOp::BvNot,
                vec![Arc::new(ChcExpr::BitVec(7, 64))],
            )),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            assert!(
                matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Div, _)),
                "x & ~7 should clear low bits via (x / 8) * 8, got: {}",
                args[0]
            );
        }
        other => panic!("x & ~7 should not fall back to UF, got: {other}"),
    }
}

/// BV64 all-ones masks must normalize the operand, not return raw Int vars (#7006).
#[test]
fn bvand_bv64_all_ones_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let bvand = ChcExpr::Op(
        ChcOp::BvAnd,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&bvand, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x & all_ones should normalize via mod 2^64, got: {result}"
    );
}

/// BV64 low-bit fill masks should encode exactly for tag packing (#7006).
#[test]
fn bvor_bv64_low_mask_sets_low_bits_7006() {
    let mut map = BvIntMap::new();
    let or = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(7, 64)),
        ],
    );
    let result = abstract_expr(&or, &mut map, false);
    match result {
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            assert!(
                matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mul, _)),
                "x | 7 should preserve high bits and rewrite low bits, got: {}",
                args[0]
            );
        }
        other => panic!("x | 7 should not fall back to UF, got: {other}"),
    }
}

/// BV64 zero-OR must normalize the operand because range constraints are skipped (#7006).
#[test]
fn bvor_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let or = ChcExpr::Op(
        ChcOp::BvOr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&or, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x | 0 should normalize via mod 2^64, got: {result}"
    );
}

/// BvXor with zero is identity, self-XOR is zero (#7006).
#[test]
fn bvxor_precise_patterns_7006() {
    let mut map = BvIntMap::new();
    let x = Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(32))));
    // x ^ 0 = x
    let xor_zero = ChcExpr::Op(
        ChcOp::BvXor,
        vec![x.clone(), Arc::new(ChcExpr::BitVec(0, 32))],
    );
    let result = abstract_expr(&xor_zero, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Var(_)),
        "x ^ 0 should be identity, got: {result}"
    );
    // x ^ x = 0
    let xor_self = ChcExpr::Op(ChcOp::BvXor, vec![x.clone(), x.clone()]);
    let result = abstract_expr(&xor_self, &mut map, false);
    assert_eq!(result, ChcExpr::int(0), "x ^ x should be 0");
}

/// BV64 zero-XOR must normalize the operand because range constraints are skipped (#7006).
#[test]
fn bvxor_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let xor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&xor, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x ^ 0 should normalize via mod 2^64, got: {result}"
    );
}

/// BV64 all-ones masks are abstracted as expression trees, not single Ints (#7006).
#[test]
fn bvxor_bv64_all_ones_encodes_as_complement_7006() {
    let mut map = BvIntMap::new();
    let xor = ChcExpr::Op(
        ChcOp::BvXor,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64)),
        ],
    );
    let result = abstract_expr(&xor, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Sub, _)),
        "x ^ 0xffff...ffff should encode as complement, got: {result}"
    );
    assert!(
        expr_contains_op(&result, &ChcOp::Mod),
        "wide complement should normalize the operand, got: {result}"
    );
}

/// BvSignExtend must properly fill high bits for negative values (#7006).
#[test]
fn bv_sign_extend_exact_encoding_7006() {
    let mut map = BvIntMap::new();
    // sign_extend[24](x) where x is BV8: BV8 → BV32
    // For x >= 128 (negative in signed): add 2^32 - 2^8 = 4294967040
    // For x < 128 (positive): identity
    let sext = ChcExpr::Op(
        ChcOp::BvSignExtend(24),
        vec![Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(8))))],
    );
    let result = abstract_expr(&sext, &mut map, false);
    // Should be an ITE: ite(x >= 128, x + fill, x)
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Ite, _)),
        "sign_extend should produce ITE for sign bit check, got: {result}"
    );
}

/// Wide sign-extension must normalize its operand before checking the sign bit.
#[test]
fn bv_sign_extend_bv64_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let sext = ChcExpr::Op(
        ChcOp::BvSignExtend(1),
        vec![Arc::new(ChcExpr::Var(ChcVar::new(
            "x",
            ChcSort::BitVec(64),
        )))],
    );
    let result = abstract_expr(&sext, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Ite, _)),
        "sign_extend should still produce ITE, got: {result}"
    );
    assert!(
        expr_contains_op(&result, &ChcOp::Mod),
        "wide sign_extend should normalize the operand, got: {result}"
    );
}

#[test]
fn bvshl_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let shl = ChcExpr::Op(
        ChcOp::BvShl,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&shl, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x << 0 should normalize via mod 2^64, got: {result}"
    );
}

#[test]
fn bvlshr_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let lshr = ChcExpr::Op(
        ChcOp::BvLShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&lshr, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x >> 0 should normalize via mod 2^64, got: {result}"
    );
}

#[test]
fn bvashr_bv64_zero_normalizes_operand_7006() {
    let mut map = BvIntMap::new();
    let ashr = ChcExpr::Op(
        ChcOp::BvAShr,
        vec![
            Arc::new(ChcExpr::Var(ChcVar::new("x", ChcSort::BitVec(64)))),
            Arc::new(ChcExpr::BitVec(0, 64)),
        ],
    );
    let result = abstract_expr(&ashr, &mut map, false);
    assert!(
        matches!(result, ChcExpr::Op(ChcOp::Mod, _)),
        "x ashr 0 should normalize via mod 2^64, got: {result}"
    );
}

/// BV64 constants >= 2^63 must not abort the BvToInt transformation (#7006).
/// Instead they should be represented as (low + high * 2^32) expressions.
#[test]
fn bv64_large_constant_no_overflow_abort_7006() {
    let mut map = BvIntMap::new();
    let problem = make_simple_bv_problem(64);
    // Add a clause with a BV64 constant >= 2^63.
    // 0xFFFFFFFFFFFFFFFF = 2^64 - 1
    let big_val = ChcExpr::BitVec(0xFFFF_FFFF_FFFF_FFFF, 64);
    let abstracted = abstract_expr(&big_val, &mut map, false);
    // Must NOT set has_overflow.
    assert!(
        !map.has_overflow,
        "BV64 max value should not trigger overflow abort"
    );
    // The result should be an Add expression: low + high * 2^32
    assert!(
        matches!(abstracted, ChcExpr::Op(ChcOp::Add, _)),
        "BV64 0xFFFFFFFFFFFFFFFF should be Add expr, got: {abstracted}"
    );

    // Test 0x8000000000000000 = 2^63 (smallest value that overflows i64)
    let mut map2 = BvIntMap::new();
    let half_val = ChcExpr::BitVec(0x8000_0000_0000_0000, 64);
    let abstracted2 = abstract_expr(&half_val, &mut map2, false);
    assert!(
        !map2.has_overflow,
        "BV64 2^63 should not trigger overflow abort"
    );
    let is_zero_plus_mul = match &abstracted2 {
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            matches!(args[0].as_ref(), ChcExpr::Int(0))
                && matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::Mul, _))
        }
        _ => false,
    };
    assert!(
        matches!(abstracted2, ChcExpr::Op(ChcOp::Mul, _)) || is_zero_plus_mul,
        "BV64 2^63 should decompose to 0 + 2^31 * 2^32, got: {abstracted2}"
    );

    // Small BV64 values should still be plain Int constants.
    let mut map3 = BvIntMap::new();
    let small_val = ChcExpr::BitVec(42, 64);
    let abstracted3 = abstract_expr(&small_val, &mut map3, false);
    assert!(!map3.has_overflow);
    assert_eq!(abstracted3, ChcExpr::int(42));

    // Verify the full transformation doesn't abort for BV64 problems.
    let mut map4 = BvIntMap::new();
    let _ = abstract_problem(&problem, &mut map4, false, false);
    assert!(
        !map4.has_overflow,
        "BV64 simple problem should not trigger overflow"
    );
}

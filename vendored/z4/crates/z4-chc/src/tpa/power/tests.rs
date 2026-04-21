// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::bool_partition::{classify_bool_partition, normalize_constraints_for_partition};
use super::*;
use crate::expr_vars::expr_var_names;
use crate::farkas::parse_linear_constraint;
use crate::tpa::TpaConfig;
use crate::{ChcProblem, ChcSort, ChcVar};
use rustc_hash::{FxHashMap, FxHashSet};

fn contains_ite(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(crate::ChcOp::Ite, _) => true,
        ChcExpr::Op(_, args) => args.iter().any(|arg| contains_ite(arg)),
        _ => false,
    }
}

#[test]
fn test_normalize_constraints_for_partition_eliminates_arithmetic_ite() {
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let mut substitutions = FxHashMap::default();
    substitutions.insert(flag.name.clone(), ChcExpr::Bool(true));

    let normalized = normalize_constraints_for_partition(
        &[ChcExpr::eq(
            ChcExpr::var(y),
            ChcExpr::ite(
                ChcExpr::var(flag),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
            ),
        )],
        &substitutions,
    );

    assert!(
        !normalized.unsat,
        "normalized branch should remain feasible"
    );
    assert!(
        normalized
            .constraints
            .iter()
            .all(|constraint| !contains_ite(constraint)),
        "normalized constraints should be ITE-free: {:?}",
        normalized.constraints
    );
    assert!(
        normalized
            .constraints
            .iter()
            .any(|constraint| parse_linear_constraint(constraint).is_some()),
        "normalized branch should expose at least one linear constraint: {:?}",
        normalized.constraints
    );
}

#[test]
fn test_full_bool_partition_interpolant_excludes_local_bools() {
    let a = ChcVar::new("a", ChcSort::Bool);
    let s = ChcVar::new("s", ChcSort::Bool);
    let b = ChcVar::new("b", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::Int);

    let a_constraints = vec![
        ChcExpr::implies(
            ChcExpr::var(a.clone()),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(a)),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::implies(
            ChcExpr::var(s.clone()),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(s.clone())),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
    ];
    let b_constraints = vec![
        ChcExpr::implies(
            ChcExpr::var(s.clone()),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(s.clone())),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ),
        ChcExpr::implies(
            ChcExpr::var(b.clone()),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5)),
        ),
        ChcExpr::implies(
            ChcExpr::not(ChcExpr::var(b)),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(6)),
        ),
    ];
    let shared_vars: FxHashSet<String> = FxHashSet::from_iter([x.name, s.name]);

    let partition = classify_bool_partition(&a_constraints, &b_constraints);
    assert_eq!(
        partition
            .a_local
            .iter()
            .map(|var| var.name.clone())
            .collect::<Vec<_>>(),
        vec!["a".to_string()]
    );
    assert_eq!(
        partition
            .shared
            .iter()
            .map(|var| var.name.clone())
            .collect::<Vec<_>>(),
        vec!["s".to_string()]
    );
    assert_eq!(
        partition
            .b_local
            .iter()
            .map(|var| var.name.clone())
            .collect::<Vec<_>>(),
        vec!["b".to_string()]
    );

    let mut solver = TpaSolver::new(ChcProblem::new(), TpaConfig::default());
    let interpolant = solver
        .interpolate_with_full_bool_partitioning(
            &a_constraints,
            &b_constraints,
            &shared_vars,
            &partition,
        )
        .expect("full Bool partitioning should produce a valid interpolant");

    assert!(
        solver.validate_recombined_interpolant(
            &a_constraints,
            &b_constraints,
            &interpolant,
            &shared_vars
        ),
        "recombined interpolant must satisfy Craig validation"
    );

    let vars = expr_var_names(&interpolant);
    assert!(
        !vars.contains("a"),
        "A-local Bool leaked into interpolant: {interpolant}"
    );
    assert!(
        !vars.contains("b"),
        "B-local Bool leaked into interpolant: {interpolant}"
    );
    assert!(
        vars.iter().all(|name| shared_vars.contains(name)),
        "interpolant must mention only shared vars, got {vars:?}"
    );
}

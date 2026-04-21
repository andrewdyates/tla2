// Copyright 2026 Andrew Yates.
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Consumer-boundary validation tests for `execute_direct` (#6852).

use super::*;

#[test]
fn test_unvalidated_sat_rejected_at_consumer_boundary_6852() {
    let mut program = Z4Program::new();
    program.set_logic("QF_FPLRA");

    let x = program.declare_const("x", Sort::fp(5, 11));
    let r = program.declare_const("r", Sort::real());
    program.assert(r.clone().eq(x.fp_to_real()));
    program.assert(r.real_gt(Expr::real(1)));
    program.check_sat();

    let details = execute_typed_with_details(&program).unwrap();
    match &details.result {
        ExecuteTypedResult::Unknown(reason) => {
            assert!(
                reason.contains("model validation did not run"),
                "unexpected consumer-boundary rejection message: {reason}"
            );
        }
        other => panic!("expected Unknown at the consumer boundary, got {other:?}"),
    }

    let degradation = details
        .degradation
        .as_ref()
        .expect("expected consumer-boundary degradation metadata");
    assert_eq!(
        degradation.kind,
        ExecuteDegradationKind::UnvalidatedSatBoundary
    );

    let solve_details = details
        .solve_details
        .as_ref()
        .expect("expected retained SAT solve details");
    assert_eq!(solve_details.result.result(), SolveResult::Sat);
    assert!(
        !solve_details.verification.sat_model_validated,
        "retained solve details should preserve the unvalidated SAT diagnostic"
    );
    assert!(details.assumption_solve_details.is_none());
}

#[test]
fn test_unknown_qf_logic_is_rejected_explicitly() {
    let mut program = Z4Program::new();
    program.set_logic("QF_FOO");

    let err = execute(&program).expect_err("unknown QF logic should not fall back");
    match err {
        ExecuteError::UnsupportedLogic(logic) => {
            assert_eq!(logic, "QF_FOO");
        }
        other => panic!("expected UnsupportedLogic for unknown QF family, got {other:?}"),
    }
}

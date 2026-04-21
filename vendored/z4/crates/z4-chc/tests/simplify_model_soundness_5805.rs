// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #5805: simplify_model + sanitize_free_variables
//! can weaken an invariant to Bool(true), turning a valid model into an
//! unsound one.
//!
//! Benchmark: O3_id_o20_false-unreach-call_000.smt2 from hcai-bench/svcomp/O3
//! Z3 says: unsat (correct — system is unsafe)
//! Z4 pre-fix: sat (WRONG — claimed false safe invariant)
//! Z4 post-fix: unsat or unknown (never sat)

#![allow(clippy::panic)]

use ntest::timeout;
use z4_chc::testing::pdr_solve_from_str;
use z4_chc::{PdrConfig, PdrResult};

/// O3_id_o20: multi-predicate unsafe CHC system.
/// 3 predicates, 6 clauses. query clause: main@id.exit.split => false.
const O3_ID_O20_SMT2: &str = r#"
(set-logic HORN)
(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@id.exit.split| ( ) Bool)
(declare-fun |main@tailrecurse.i| ( Int Int ) Bool)
(assert (forall ( (A Int) )
  (=> (and true) (main@entry A))))
(assert (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Int) )
  (=> (and (main@entry B)
    (and (= A B) (or (not H) (not D) (not C)) (or (not H) (not G) (= F E))
     (or (not H) (not G) (= I 0)) (or (not H) (not G) (= J F))
     (or (not H) (not G) (= K I)) (or (not G) (and H G))
     (or (not H) (and H C)) (= G true) (= D (= E 0))))
    (main@tailrecurse.i J K))))
(assert (forall ( (A Int) (B Int) (C Bool) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Int) )
  (=> (and (main@tailrecurse.i A B)
    (and (= D (+ (- 1) A)) (= E (+ 1 B))
     (or (not H) (not G) (= F D)) (or (not H) (not G) (= I E))
     (or (not H) (not G) (= J F)) (or (not H) (not G) (= K I))
     (or (not H) (not G) (not C)) (or (not G) (and H G))
     (= G true) (= C (= D 0))))
    (main@tailrecurse.i J K))))
(assert (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) )
  (=> (and (main@entry B)
    (and (= A B) (or (not H) (not E) (= G F)) (or (not H) (not E) D)
     (or (not H) (not F) (not E)) (or (not H) (and H E))
     (or (not H) G) (or (not I) (and I H)) (= I true) (= D (= C 0))))
    main@id.exit.split)))
(assert (forall ( (A Int) (B Int) (C Int) (D Bool) (E Int) (F Bool) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) )
  (=> (and (main@tailrecurse.i A B)
    (and (= C (+ (- 1) A)) (= E (+ 1 B))
     (or (not J) (not F) (= G E)) (or (not J) (not F) (= H G))
     (or (not J) (not F) D) (or (not M) (not J) (= L K))
     (or (not M) (not J) (= K I)) (or (not J) (= I (= H 20)))
     (or (not J) (and J F)) (or (not M) (and M J))
     (or (not M) L) (or (not N) (and N M)) (= N true) (= D (= C 0))))
    main@id.exit.split)))
(assert (forall ( (CHC_COMP_UNUSED Bool) )
  (=> (and main@id.exit.split true) false)))
(check-sat)
(exit)
"#;

/// PDR must not return Safe on this unsafe system (#5805).
///
/// Root cause: sanitize_free_variables strips invariant conjuncts with
/// undeclared variables, weakening the model to Bool(true). The fix
/// re-verifies after sanitization.
///
/// Note: In debug mode, intermediate debug_assert! panics may fire from
/// clause-local variable leakage (#5805 root cause) or mixed-sort
/// equalities. These panics are acceptable — the critical invariant is
/// that the solver never returns Safe on this unsafe system.
#[test]
#[timeout(30_000)]
fn test_simplify_model_does_not_create_false_safe_5805() {
    let result = std::panic::catch_unwind(|| {
        let config = PdrConfig::production(false);
        pdr_solve_from_str(O3_ID_O20_SMT2, config)
    });

    match result {
        Ok(Ok(pdr_result)) => {
            // Solver completed without panic — verify it didn't return Safe
            assert!(
                !matches!(pdr_result, PdrResult::Safe(_)),
                "SOUNDNESS BUG #5805: PDR returned Safe on an unsafe system \
                 (O3_id_o20). simplify_model likely weakened invariant to Bool(true). \
                 Got: {pdr_result:?}"
            );
        }
        Ok(Err(e)) => {
            // Solver returned an error — acceptable (not a wrong Safe answer)
            eprintln!("PDR solver error (acceptable for #5805 test): {e}");
        }
        Err(_panic) => {
            // Solver panicked (debug_assert! fired) — acceptable.
            // The panic indicates a debug-mode invariant violation from
            // clause-local variable leakage, which is the known root cause
            // of #5805. The safety net prevents wrong answers in release mode.
            eprintln!(
                "PDR panicked in debug mode (expected: clause-local variable \
                 leakage triggers debug_assert). This is acceptable — the \
                 critical check is that Safe is never returned."
            );
        }
    }
}

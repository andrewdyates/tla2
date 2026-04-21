// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(deprecated)] // Tests exercise the deprecated TranslationContext::new API

use super::*;
use crate::{TranslationContext, TranslationSession, TranslationState};
use z4_dpll::api::{Logic, Solver};

#[test]
fn test_uf_declare_and_apply_with_session() {
    let mut state: TranslationState<String> = TranslationState::new();
    let mut solver = Solver::try_new(Logic::QfUf).expect("QfUf should be supported");
    let result = {
        let mut session = TranslationSession::new(&mut solver, &mut state);
        let func = declare(&mut session, "f", &[Sort::Int], Sort::Int);
        let x = session.get_or_declare("x".to_string(), "x", Sort::Int);
        let app = apply(&mut session, &func, &[x]);
        let eq = session
            .solver()
            .try_eq(app, x)
            .expect("UF application should compare to Int");
        session.assert_term(eq);
        session.check_sat()
    };

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
    assert_eq!(state.func_count(), 1);
}

#[test]
fn test_uf_declare_and_apply_with_context() {
    let mut ctx: TranslationContext<String> = TranslationContext::new(Logic::QfUf);
    let func = declare(&mut ctx, "f", &[Sort::Int], Sort::Int);
    let x = ctx.get_or_declare("x".to_string(), "x", Sort::Int);
    let app = apply(&mut ctx, &func, &[x]);
    let eq = ctx
        .solver()
        .try_eq(app, x)
        .expect("UF application should compare to Int");
    ctx.assert_term(eq);
    let result = ctx.check_sat();

    assert!(result.is_sat(), "Expected Sat, got {result:?}");
    assert_eq!(ctx.state().func_count(), 1);
}

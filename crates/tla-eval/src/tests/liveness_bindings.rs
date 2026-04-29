// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::binding_chain::BindingChain;
use crate::eval;
use crate::EvalCtx;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::name_intern::intern_name;
use tla_core::Spanned;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn liveness_bindings_shadow_ident_but_not_state_var() {
    let mut ctx = EvalCtx::new();
    let p_name = intern_name("p");
    ctx.register_var("p");
    let state = vec![Value::int(0)];
    ctx.bind_state_array(&state);

    let liveness_chain = BindingChain::from_values([(Arc::from("p"), Value::int(2), p_name)]);
    let liveness_ctx = ctx.with_liveness_bindings(&liveness_chain);

    let ident = Spanned::dummy(Expr::Ident("p".to_string(), p_name));
    let state_var = Spanned::dummy(Expr::StateVar("p".to_string(), 0, p_name));

    assert_eq!(
        eval(&liveness_ctx, &ident).expect("Ident should resolve liveness binding"),
        Value::int(2)
    );
    assert_eq!(
        eval(&liveness_ctx, &state_var).expect("StateVar should resolve state slot"),
        Value::int(0)
    );
}

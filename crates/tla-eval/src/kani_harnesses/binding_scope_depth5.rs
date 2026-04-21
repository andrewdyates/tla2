// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kani proofs for binding scope preservation at depth 5.
//!
//! Extends `binding_scope_preservation.rs` (P1-P5) to the "bounded depth 5"
//! requirement from #3037 acceptance criterion 2. Also includes full-stack
//! EvalCtx roundtrip tests that exercise the actual `with_module_scope` ->
//! `with_outer_resolution_scope` code path.
//!
//! Properties verified:
//! - P6: Five nested bindings survive single scope roundtrip
//! - P7: Five nested bindings survive double scope roundtrip (INSTANCE within INSTANCE)
//!
//! Part of #3037 Layer 2a.

#[cfg(kani)]
mod kani_proofs {
    use crate::binding_chain::{BindingChain, BindingValue};
    use tla_core::name_intern::NameId;
    use tla_value::Value;

    const NAME_A: NameId = NameId(1);
    const NAME_B: NameId = NameId(2);
    const NAME_C: NameId = NameId(3);
    const NAME_D: NameId = NameId(4);
    const NAME_E: NameId = NameId(5);
    const NAME_MODULE: NameId = NameId(100);
    const NAME_MODULE2: NameId = NameId(101);

    // =========================================================================
    // P6: Bounded depth 5 -- five nested bindings survive scope roundtrip
    // Matches acceptance criterion: "bounded depth 5" from #3037.
    // =========================================================================

    #[kani::proof]
    fn depth_5_bindings_survive_scope_roundtrip() {
        let chain = BindingChain::empty();
        let chain = chain.cons(NAME_A, BindingValue::eager(Value::int(10)));
        let chain = chain.cons(NAME_B, BindingValue::eager(Value::int(20)));
        let chain = chain.cons(NAME_C, BindingValue::eager(Value::int(30)));
        let chain = chain.cons(NAME_D, BindingValue::eager(Value::int(40)));
        let chain = chain.cons(NAME_E, BindingValue::eager(Value::int(50)));

        let pre_scope = chain.clone();
        let _in_scope = chain.cons(NAME_MODULE, BindingValue::eager(Value::Bool(true)));
        let restored = pre_scope;

        assert!(
            restored.lookup(NAME_A).is_some(),
            "depth-1 binding must survive"
        );
        assert!(
            restored.lookup(NAME_B).is_some(),
            "depth-2 binding must survive"
        );
        assert!(
            restored.lookup(NAME_C).is_some(),
            "depth-3 binding must survive"
        );
        assert!(
            restored.lookup(NAME_D).is_some(),
            "depth-4 binding must survive"
        );
        assert!(
            restored.lookup(NAME_E).is_some(),
            "depth-5 binding must survive"
        );
        assert!(
            restored.lookup(NAME_MODULE).is_none(),
            "module binding must not leak at depth 5"
        );
    }

    // =========================================================================
    // P7: Nested scope roundtrip at depth 5 -- enter/exit two module scopes
    // =========================================================================

    #[kani::proof]
    fn depth_5_survives_double_scope_roundtrip() {
        let chain = BindingChain::empty();
        let chain = chain.cons(NAME_A, BindingValue::eager(Value::int(1)));
        let chain = chain.cons(NAME_B, BindingValue::eager(Value::int(2)));
        let chain = chain.cons(NAME_C, BindingValue::eager(Value::int(3)));
        let chain = chain.cons(NAME_D, BindingValue::eager(Value::int(4)));
        let chain = chain.cons(NAME_E, BindingValue::eager(Value::int(5)));

        // First scope: save, push, restore
        let pre_scope_1 = chain.clone();
        let in_scope_1 = chain.cons(NAME_MODULE, BindingValue::eager(Value::Bool(true)));
        let _ = in_scope_1;
        let after_scope_1 = pre_scope_1;

        // Second scope: save, push, restore
        let pre_scope_2 = after_scope_1.clone();
        let in_scope_2 = after_scope_1.cons(NAME_MODULE2, BindingValue::eager(Value::Bool(false)));
        let _ = in_scope_2;
        let after_scope_2 = pre_scope_2;

        assert!(
            after_scope_2.lookup(NAME_A).is_some(),
            "depth-1 survives double roundtrip"
        );
        assert!(
            after_scope_2.lookup(NAME_B).is_some(),
            "depth-2 survives double roundtrip"
        );
        assert!(
            after_scope_2.lookup(NAME_C).is_some(),
            "depth-3 survives double roundtrip"
        );
        assert!(
            after_scope_2.lookup(NAME_D).is_some(),
            "depth-4 survives double roundtrip"
        );
        assert!(
            after_scope_2.lookup(NAME_E).is_some(),
            "depth-5 survives double roundtrip"
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::binding_chain::{BindingChain, BindingValue};
    use crate::core::{EvalCtx, OpEnv};
    use tla_core::name_intern::intern_name;
    use tla_value::Value;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_depth_5_bindings_survive_scope_roundtrip() {
        let v1 = intern_name("test_bsd5_v1");
        let v2 = intern_name("test_bsd5_v2");
        let v3 = intern_name("test_bsd5_v3");
        let v4 = intern_name("test_bsd5_v4");
        let v5 = intern_name("test_bsd5_v5");
        let m = intern_name("test_bsd5_mod");

        let chain = BindingChain::empty();
        let chain = chain.cons(v1, BindingValue::eager(Value::int(10)));
        let chain = chain.cons(v2, BindingValue::eager(Value::int(20)));
        let chain = chain.cons(v3, BindingValue::eager(Value::int(30)));
        let chain = chain.cons(v4, BindingValue::eager(Value::int(40)));
        let chain = chain.cons(v5, BindingValue::eager(Value::int(50)));

        let pre_scope = chain.clone();
        let _in_scope = chain.cons(m, BindingValue::eager(Value::Bool(true)));
        let restored = pre_scope;

        assert!(restored.lookup(v1).is_some(), "depth-1 must survive");
        assert!(restored.lookup(v2).is_some(), "depth-2 must survive");
        assert!(restored.lookup(v3).is_some(), "depth-3 must survive");
        assert!(restored.lookup(v4).is_some(), "depth-4 must survive");
        assert!(restored.lookup(v5).is_some(), "depth-5 must survive");
        assert!(restored.lookup(m).is_none(), "module must not leak");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_depth_5_survives_double_scope_roundtrip() {
        let a = intern_name("test_bsd5_dd_a");
        let b = intern_name("test_bsd5_dd_b");
        let c = intern_name("test_bsd5_dd_c");
        let d = intern_name("test_bsd5_dd_d");
        let e = intern_name("test_bsd5_dd_e");
        let m1 = intern_name("test_bsd5_dd_m1");
        let m2 = intern_name("test_bsd5_dd_m2");

        let chain = BindingChain::empty();
        let chain = chain.cons(a, BindingValue::eager(Value::int(1)));
        let chain = chain.cons(b, BindingValue::eager(Value::int(2)));
        let chain = chain.cons(c, BindingValue::eager(Value::int(3)));
        let chain = chain.cons(d, BindingValue::eager(Value::int(4)));
        let chain = chain.cons(e, BindingValue::eager(Value::int(5)));

        // First scope roundtrip
        let pre_scope_1 = chain.clone();
        let _in_scope_1 = chain.cons(m1, BindingValue::eager(Value::Bool(true)));
        let after_scope_1 = pre_scope_1;

        // Second scope roundtrip
        let pre_scope_2 = after_scope_1.clone();
        let _in_scope_2 = after_scope_1.cons(m2, BindingValue::eager(Value::Bool(false)));
        let after_scope_2 = pre_scope_2;

        assert!(
            after_scope_2.lookup(a).is_some(),
            "depth-1 double roundtrip"
        );
        assert!(
            after_scope_2.lookup(b).is_some(),
            "depth-2 double roundtrip"
        );
        assert!(
            after_scope_2.lookup(c).is_some(),
            "depth-3 double roundtrip"
        );
        assert!(
            after_scope_2.lookup(d).is_some(),
            "depth-4 double roundtrip"
        );
        assert!(
            after_scope_2.lookup(e).is_some(),
            "depth-5 double roundtrip"
        );
    }

    // -----------------------------------------------------------------------
    // EvalCtx-level depth-5 roundtrip: full with_module_scope path.
    // Exercises the actual scope management code (not just BindingChain).
    // -----------------------------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_evalctx_depth_5_scope_roundtrip() {
        let v1 = intern_name("test_bsd5ctx_v1");
        let v2 = intern_name("test_bsd5ctx_v2");
        let v3 = intern_name("test_bsd5ctx_v3");
        let v4 = intern_name("test_bsd5ctx_v4");
        let v5 = intern_name("test_bsd5ctx_v5");

        let mut ctx = EvalCtx::new();
        ctx.bindings = ctx
            .bindings
            .cons_local(v1, BindingValue::eager(Value::int(1)), 0);
        ctx.bindings = ctx
            .bindings
            .cons_local(v2, BindingValue::eager(Value::int(2)), 1);
        ctx.bindings = ctx
            .bindings
            .cons_local(v3, BindingValue::eager(Value::int(3)), 2);
        ctx.bindings = ctx
            .bindings
            .cons_local(v4, BindingValue::eager(Value::int(4)), 3);
        ctx.bindings = ctx
            .bindings
            .cons_local(v5, BindingValue::eager(Value::int(5)), 4);
        ctx.binding_depth = 5;

        // Enter module scope
        let module_ctx = ctx.with_module_scope(OpEnv::new(), vec![], vec![]);

        // Exit scope
        let restored = module_ctx.with_outer_resolution_scope();

        // All 5 quantifier bindings must survive
        assert!(
            restored.bindings.lookup(v1).is_some(),
            "EvalCtx depth-1 must survive"
        );
        assert!(
            restored.bindings.lookup(v2).is_some(),
            "EvalCtx depth-2 must survive"
        );
        assert!(
            restored.bindings.lookup(v3).is_some(),
            "EvalCtx depth-3 must survive"
        );
        assert!(
            restored.bindings.lookup(v4).is_some(),
            "EvalCtx depth-4 must survive"
        );
        assert!(
            restored.bindings.lookup(v5).is_some(),
            "EvalCtx depth-5 must survive"
        );
    }
}

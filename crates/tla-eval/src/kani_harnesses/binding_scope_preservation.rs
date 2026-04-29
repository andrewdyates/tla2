// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kani proofs for binding chain scope preservation.
//!
//! Verifies that quantifier/parameter bindings survive INSTANCE scope transitions.
//! This is the property that broke in #3030 (MCYoYoPruning "Undefined variable: n"):
//! `with_outer_resolution_scope()` was clearing the binding chain entirely
//! instead of restoring the pre-scope snapshot.
//!
//! Properties verified:
//! - P1: BindingChain cons preserves existing lookups
//! - P2: BindingChain clone preserves all lookups (pre_scope_bindings pattern)
//! - P3: Scope roundtrip: bindings pushed before scope entry survive scope exit
//! - P4: Module-scope bindings do NOT survive scope exit
//! - P5: Multiple pre-scope bindings are all preserved
//!
//! Part of #3037 Layer 2a.

#[cfg(kani)]
mod kani_proofs {
    use crate::binding_chain::{BindingChain, BindingValue};
    use tla_core::name_intern::NameId;
    use tla_value::Value;

    // Use concrete NameIds to avoid global interner dependency in Kani.
    const NAME_A: NameId = NameId(1);
    const NAME_B: NameId = NameId(2);
    const NAME_C: NameId = NameId(3);
    const NAME_MODULE: NameId = NameId(100);

    // =========================================================================
    // P1: cons preserves existing lookups
    // Adding a new binding does not shadow or destroy existing bindings
    // with different names. This is the core immutable linked list property
    // that TLC's Context.java relies on.
    // =========================================================================

    #[kani::proof]
    fn cons_preserves_existing_lookup() {
        let chain = BindingChain::empty();
        let chain = chain.cons(NAME_A, BindingValue::eager(Value::int(42)));

        // Push a different name
        let chain2 = chain.cons(NAME_B, BindingValue::eager(Value::int(99)));

        // Original binding must still be visible
        let lookup_a = chain2.lookup(NAME_A);
        assert!(lookup_a.is_some(), "binding 'a' must survive cons of 'b'");
    }

    // =========================================================================
    // P2: Clone preserves all lookups (the pre_scope_bindings mechanism)
    // with_module_scope_shared saves `ctx.bindings.clone()` as pre_scope_bindings.
    // The clone must preserve all existing lookups regardless of subsequent
    // mutations to the original chain (which is impossible since chains are
    // immutable -- but we verify the contract).
    // =========================================================================

    #[kani::proof]
    fn clone_preserves_all_lookups() {
        let chain = BindingChain::empty();
        let chain = chain.cons(NAME_A, BindingValue::eager(Value::int(1)));
        let chain = chain.cons(NAME_B, BindingValue::eager(Value::int(2)));

        // Clone = pre_scope_bindings snapshot
        let saved = chain.clone();

        // Push more bindings onto original (simulates module scope entry)
        let _extended = chain.cons(NAME_C, BindingValue::eager(Value::int(3)));

        // Saved chain must still have both bindings
        assert!(saved.lookup(NAME_A).is_some(), "'a' must survive in clone");
        assert!(saved.lookup(NAME_B).is_some(), "'b' must survive in clone");
    }

    // =========================================================================
    // P3: Scope roundtrip -- pre-scope bindings survive scope exit
    // This simulates the with_module_scope -> with_outer_resolution_scope
    // pattern. The pre-scope chain is saved, module bindings are pushed, then
    // the pre-scope chain is restored. All original bindings must be visible.
    // =========================================================================

    #[kani::proof]
    fn scope_roundtrip_preserves_pre_scope_bindings() {
        // Phase 1: Quantifier binding pushed before INSTANCE scope
        let chain = BindingChain::empty();
        let chain = chain.cons(NAME_A, BindingValue::eager(Value::int(7)));

        // Phase 2: Save pre-scope (what with_module_scope_shared does)
        let pre_scope = chain.clone();

        // Phase 3: Push module-scope bindings (simulates INSTANCE scope entry)
        let _in_scope = chain.cons(NAME_MODULE, BindingValue::eager(Value::Bool(true)));

        // Phase 4: Restore pre-scope (what with_outer_resolution_scope does)
        let restored = pre_scope;

        // The quantifier binding 'n' must be visible after restoration.
        // This is the exact assertion that would have caught #3030.
        let lookup = restored.lookup(NAME_A);
        assert!(
            lookup.is_some(),
            "quantifier binding must survive INSTANCE scope roundtrip"
        );
    }

    // =========================================================================
    // P4: Module-scope bindings do NOT leak through scope exit
    // When pre_scope_bindings is restored, bindings added during module scope
    // (e.g., INSTANCE operator params) must NOT be in the restored chain.
    // =========================================================================

    #[kani::proof]
    fn module_scope_bindings_do_not_survive_exit() {
        let chain = BindingChain::empty();
        let chain = chain.cons(NAME_A, BindingValue::eager(Value::int(1)));

        // Save pre-scope
        let pre_scope = chain.clone();

        // Push module-scope binding
        let in_scope = chain.cons(NAME_MODULE, BindingValue::eager(Value::Bool(true)));

        // Module binding IS visible in-scope
        assert!(
            in_scope.lookup(NAME_MODULE).is_some(),
            "module binding must be visible in-scope"
        );

        // Restore pre-scope
        let restored = pre_scope;

        // Module binding must NOT be visible after restore
        assert!(
            restored.lookup(NAME_MODULE).is_none(),
            "module binding must not leak through scope exit"
        );
    }

    // =========================================================================
    // P5: Multiple pre-scope bindings are all preserved
    // Verifies the property for chains of depth > 1 -- the typical case when
    // nested quantifiers are active during INSTANCE resolution.
    // =========================================================================

    #[kani::proof]
    fn multiple_pre_scope_bindings_all_preserved() {
        let chain = BindingChain::empty();
        let chain = chain.cons(NAME_A, BindingValue::eager(Value::int(1)));
        let chain = chain.cons(NAME_B, BindingValue::eager(Value::int(2)));
        let chain = chain.cons(NAME_C, BindingValue::eager(Value::int(3)));

        // Save pre-scope
        let pre_scope = chain.clone();

        // Push module binding (overwrites chain variable but not the saved snapshot)
        let _in_scope = chain.cons(NAME_MODULE, BindingValue::eager(Value::Bool(false)));

        // Restore
        let restored = pre_scope;

        // All three quantifier bindings must be visible
        assert!(
            restored.lookup(NAME_A).is_some(),
            "binding 'x' must survive scope roundtrip"
        );
        assert!(
            restored.lookup(NAME_B).is_some(),
            "binding 'y' must survive scope roundtrip"
        );
        assert!(
            restored.lookup(NAME_C).is_some(),
            "binding 'z' must survive scope roundtrip"
        );
    }
}

// =========================================================================
// Test mirrors: verify the same properties using #[test] for fast CI feedback.
// Additionally, test the full EvalCtx roundtrip (requires runtime infrastructure
// that Kani cannot handle).
// =========================================================================

#[cfg(test)]
mod tests {
    use crate::binding_chain::{BindingChain, BindingValue};
    use crate::core::{EvalCtx, OpEnv};
    use tla_core::name_intern::intern_name;
    use tla_value::Value;

    // -----------------------------------------------------------------------
    // BindingChain-level tests (mirror Kani proofs)
    // -----------------------------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_cons_preserves_existing_lookup() {
        let a = intern_name("test_bsp_a");
        let b = intern_name("test_bsp_b");
        let chain = BindingChain::empty();
        let chain = chain.cons(a, BindingValue::eager(Value::int(42)));
        let chain2 = chain.cons(b, BindingValue::eager(Value::int(99)));

        assert!(
            chain2.lookup(a).is_some(),
            "binding 'a' must survive cons of 'b'"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_clone_preserves_all_lookups() {
        let a = intern_name("test_bsp_ca");
        let b = intern_name("test_bsp_cb");
        let c = intern_name("test_bsp_cc");
        let chain = BindingChain::empty();
        let chain = chain.cons(a, BindingValue::eager(Value::int(1)));
        let chain = chain.cons(b, BindingValue::eager(Value::int(2)));

        let saved = chain.clone();
        let _extended = chain.cons(c, BindingValue::eager(Value::int(3)));

        assert!(saved.lookup(a).is_some());
        assert!(saved.lookup(b).is_some());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_scope_roundtrip_preserves_pre_scope_bindings() {
        let n = intern_name("test_bsp_n");
        let m = intern_name("test_bsp_module_op");
        let chain = BindingChain::empty();
        let chain = chain.cons(n, BindingValue::eager(Value::int(7)));

        let pre_scope = chain.clone();
        let _in_scope = chain.cons(m, BindingValue::eager(Value::Bool(true)));
        let restored = pre_scope;

        assert!(
            restored.lookup(n).is_some(),
            "quantifier binding must survive roundtrip"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_module_scope_bindings_do_not_survive_exit() {
        let n = intern_name("test_bsp_n2");
        let m = intern_name("test_bsp_mod2");
        let chain = BindingChain::empty();
        let chain = chain.cons(n, BindingValue::eager(Value::int(1)));

        let pre_scope = chain.clone();
        let in_scope = chain.cons(m, BindingValue::eager(Value::Bool(true)));

        assert!(in_scope.lookup(m).is_some());
        let restored = pre_scope;
        assert!(restored.lookup(m).is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_multiple_pre_scope_bindings_all_preserved() {
        let x = intern_name("test_bsp_x");
        let y = intern_name("test_bsp_y");
        let z = intern_name("test_bsp_z");
        let m = intern_name("test_bsp_m3");
        let chain = BindingChain::empty();
        let chain = chain.cons(x, BindingValue::eager(Value::int(1)));
        let chain = chain.cons(y, BindingValue::eager(Value::int(2)));
        let chain = chain.cons(z, BindingValue::eager(Value::int(3)));

        let pre_scope = chain.clone();
        let _in_scope = chain.cons(m, BindingValue::eager(Value::Bool(false)));
        let restored = pre_scope;

        assert!(restored.lookup(x).is_some(), "'x' must survive");
        assert!(restored.lookup(y).is_some(), "'y' must survive");
        assert!(restored.lookup(z).is_some(), "'z' must survive");
    }

    // -----------------------------------------------------------------------
    // EvalCtx-level roundtrip test (not in Kani -- too complex for CBMC)
    // Exercises the actual with_module_scope -> with_outer_resolution_scope path.
    // -----------------------------------------------------------------------

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_evalctx_scope_roundtrip_preserves_quantifier_binding() {
        let n = intern_name("test_bsp_quant_n");

        // Step 1: Create context with a quantifier binding
        let mut ctx = EvalCtx::new();
        ctx.bindings = ctx
            .bindings
            .cons_local(n, BindingValue::eager(Value::int(42)), 0);
        ctx.binding_depth = 1;

        // Verify binding is visible
        assert!(ctx.bindings.lookup(n).is_some(), "binding must be set");

        // Step 2: Enter module scope (adds module-level bindings + substitutions)
        let module_ctx = ctx.with_module_scope(OpEnv::new(), vec![], vec![]);

        // Step 3: Exit scope via with_outer_resolution_scope
        let restored_ctx = module_ctx.with_outer_resolution_scope();

        // Step 4: Quantifier binding must still be visible (the #3030 regression)
        let lookup = restored_ctx.bindings.lookup(n);
        assert!(
            lookup.is_some(),
            "quantifier binding 'n' must survive with_module_scope -> \
             with_outer_resolution_scope roundtrip (regression #3030)"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_evalctx_nested_scopes_preserve_outer_bindings() {
        let x = intern_name("test_bsp_outer_x");
        let y = intern_name("test_bsp_inner_y");

        // Step 1: Two quantifier bindings at different depths
        let mut ctx = EvalCtx::new();
        ctx.bindings = ctx
            .bindings
            .cons_local(x, BindingValue::eager(Value::int(10)), 0);
        ctx.binding_depth = 1;
        ctx.bindings = ctx
            .bindings
            .cons_local(y, BindingValue::eager(Value::int(20)), 1);
        ctx.binding_depth = 2;

        // Step 2: Enter module scope
        let module_ctx = ctx.with_module_scope(OpEnv::new(), vec![], vec![]);

        // Step 3: Exit scope
        let restored = module_ctx.with_outer_resolution_scope();

        // Step 4: Both bindings must survive
        assert!(
            restored.bindings.lookup(x).is_some(),
            "outer binding 'x' must survive nested scope roundtrip"
        );
        assert!(
            restored.bindings.lookup(y).is_some(),
            "inner binding 'y' must survive nested scope roundtrip"
        );
    }
}

// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kani proofs for property classification stability.
//!
//! Verifies that `contains_module_ref` and `contains_temporal_standalone`
//! classification depends ONLY on AST structure — not on runtime state,
//! cache state, or evaluation context. This is the property that broke
//! when property_classify.rs lost the contains_module_ref guard (#2995).
//!
//! Properties verified:
//! - P1: Determinism of contains_module_ref (idempotent)
//! - P2: Determinism of contains_temporal_standalone (idempotent)
//! - P3: Leaf nodes are neither module_ref nor temporal
//! - P4: ModuleRef nodes are correctly detected
//! - P5: Temporal operators (Always) are correctly detected
//! - P6: ModuleRef is not classified as temporal (mutual exclusion at leaf)
//! - P7: Nesting in And/Not does not hide ModuleRef
//! - P8: Nesting in And/Not does not hide temporal operators
//!
//! Part of #3037 Layer 2b.

#[cfg(kani)]
mod kani_proofs {
    use crate::check::{expr_contains, ScanDecision};
    use crate::checker_ops::{contains_module_ref, contains_temporal_standalone};
    use tla_core::ast::{Expr, ModuleTarget};
    use tla_core::name_intern::NameId;
    use tla_core::Spanned;

    // =========================================================================
    // Helpers: generate small concrete expression trees
    // =========================================================================

    fn any_leaf() -> Expr {
        let choice: u8 = kani::any();
        kani::assume(choice < 3);
        match choice {
            0 => Expr::Bool(kani::any()),
            1 => Expr::Ident("x".to_string(), NameId::INVALID),
            _ => Expr::String("s".to_string()),
        }
    }

    fn module_ref() -> Expr {
        Expr::ModuleRef(
            ModuleTarget::Named("M".to_string()),
            "Op".to_string(),
            vec![],
        )
    }

    fn always_expr(inner: Expr) -> Expr {
        Expr::Always(Box::new(Spanned::dummy(inner)))
    }

    fn and_expr(left: Expr, right: Expr) -> Expr {
        Expr::And(
            Box::new(Spanned::dummy(left)),
            Box::new(Spanned::dummy(right)),
        )
    }

    fn not_expr(inner: Expr) -> Expr {
        Expr::Not(Box::new(Spanned::dummy(inner)))
    }

    // =========================================================================
    // P1: Determinism of contains_module_ref
    // =========================================================================

    #[kani::proof]
    fn contains_module_ref_is_deterministic() {
        let choice: u8 = kani::any();
        kani::assume(choice < 4);

        let expr = match choice {
            0 => any_leaf(),
            1 => module_ref(),
            2 => and_expr(any_leaf(), module_ref()),
            _ => not_expr(any_leaf()),
        };

        let r1 = contains_module_ref(&expr);
        let r2 = contains_module_ref(&expr);
        assert_eq!(r1, r2, "contains_module_ref must be deterministic");
    }

    // =========================================================================
    // P2: Determinism of contains_temporal_standalone
    // =========================================================================

    #[kani::proof]
    fn contains_temporal_is_deterministic() {
        let choice: u8 = kani::any();
        kani::assume(choice < 4);

        let expr = match choice {
            0 => any_leaf(),
            1 => always_expr(Expr::Bool(true)),
            2 => and_expr(any_leaf(), always_expr(Expr::Bool(true))),
            _ => not_expr(any_leaf()),
        };

        let r1 = contains_temporal_standalone(&expr);
        let r2 = contains_temporal_standalone(&expr);
        assert_eq!(r1, r2, "contains_temporal must be deterministic");
    }

    // =========================================================================
    // P3: Leaf nodes are neither module_ref nor temporal
    // =========================================================================

    #[kani::proof]
    fn leaf_is_neither_module_ref_nor_temporal() {
        let b: bool = kani::any();
        let leaf = Expr::Bool(b);
        assert!(
            !contains_module_ref(&leaf),
            "Bool leaf must not be module_ref"
        );
        assert!(
            !contains_temporal_standalone(&leaf),
            "Bool leaf must not be temporal"
        );
    }

    // =========================================================================
    // P4: ModuleRef is detected
    // =========================================================================

    #[kani::proof]
    fn module_ref_is_detected() {
        let mr = module_ref();
        assert!(
            contains_module_ref(&mr),
            "ModuleRef must be detected by contains_module_ref"
        );
    }

    // =========================================================================
    // P5: Always is temporal
    // =========================================================================

    #[kani::proof]
    fn always_is_temporal() {
        let a = always_expr(Expr::Bool(true));
        assert!(
            contains_temporal_standalone(&a),
            "Always must be detected as temporal"
        );
    }

    // =========================================================================
    // P6: ModuleRef is not temporal (mutual exclusion at leaf level)
    // =========================================================================

    #[kani::proof]
    fn module_ref_is_not_temporal() {
        let mr = module_ref();
        assert!(
            !contains_temporal_standalone(&mr),
            "ModuleRef alone must not be classified as temporal"
        );
    }

    // =========================================================================
    // P7: Nesting in And/Not does not hide ModuleRef
    // =========================================================================

    #[kani::proof]
    fn nested_module_ref_detected_in_and() {
        let expr = and_expr(Expr::Bool(true), module_ref());
        assert!(
            contains_module_ref(&expr),
            "ModuleRef nested in And must be detected"
        );
    }

    #[kani::proof]
    fn nested_module_ref_detected_in_not() {
        let expr = not_expr(module_ref());
        assert!(
            contains_module_ref(&expr),
            "ModuleRef nested in Not must be detected"
        );
    }

    // =========================================================================
    // P8: Nesting in And/Not does not hide temporal operators
    // =========================================================================

    #[kani::proof]
    fn nested_always_detected_in_and() {
        let expr = and_expr(Expr::Bool(true), always_expr(Expr::Bool(false)));
        assert!(
            contains_temporal_standalone(&expr),
            "Always nested in And must be detected"
        );
    }

    #[kani::proof]
    fn nested_always_detected_in_not() {
        let expr = not_expr(always_expr(Expr::Bool(true)));
        assert!(
            contains_temporal_standalone(&expr),
            "Always nested in Not must be detected"
        );
    }
}

// =========================================================================
// Test mirrors: verify the same properties using #[test] for fast CI feedback
// =========================================================================

#[cfg(test)]
mod tests {
    use crate::checker_ops::{contains_module_ref, contains_temporal_standalone};
    use tla_core::ast::{Expr, ModuleTarget};
    use tla_core::Spanned;

    fn module_ref() -> Expr {
        Expr::ModuleRef(
            ModuleTarget::Named("M".to_string()),
            "Op".to_string(),
            vec![],
        )
    }

    fn always_expr(inner: Expr) -> Expr {
        Expr::Always(Box::new(Spanned::dummy(inner)))
    }

    fn and_expr(left: Expr, right: Expr) -> Expr {
        Expr::And(
            Box::new(Spanned::dummy(left)),
            Box::new(Spanned::dummy(right)),
        )
    }

    fn not_expr(inner: Expr) -> Expr {
        Expr::Not(Box::new(Spanned::dummy(inner)))
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_leaf_is_neither() {
        assert!(!contains_module_ref(&Expr::Bool(true)));
        assert!(!contains_temporal_standalone(&Expr::Bool(true)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_module_ref_detected() {
        assert!(contains_module_ref(&module_ref()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_always_is_temporal() {
        assert!(contains_temporal_standalone(&always_expr(Expr::Bool(true))));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_module_ref_not_temporal() {
        assert!(!contains_temporal_standalone(&module_ref()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_nested_module_ref_in_and() {
        assert!(contains_module_ref(&and_expr(
            Expr::Bool(true),
            module_ref()
        )));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_nested_module_ref_in_not() {
        assert!(contains_module_ref(&not_expr(module_ref())));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_nested_always_in_and() {
        assert!(contains_temporal_standalone(&and_expr(
            Expr::Bool(true),
            always_expr(Expr::Bool(false))
        )));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_nested_always_in_not() {
        assert!(contains_temporal_standalone(&not_expr(always_expr(
            Expr::Bool(true)
        ))));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_determinism() {
        let mr = module_ref();
        assert_eq!(contains_module_ref(&mr), contains_module_ref(&mr));

        let a = always_expr(Expr::Bool(true));
        assert_eq!(
            contains_temporal_standalone(&a),
            contains_temporal_standalone(&a)
        );
    }
}

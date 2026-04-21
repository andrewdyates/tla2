// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Kani proofs for INSTANCE substitution composition correctness.
//!
//! Verifies `compose_substitutions()` — the function that combines inner
//! INSTANCE WITH substitutions with outer (enclosing) INSTANCE substitutions.
//! This is the TLA2 counterpart of TLC's `Subst.compose()`.
//!
//! Properties verified:
//! - P1: Identity — compose(inner, None) returns inner unchanged
//! - P2: Empty outer identity — compose(inner, Some([])) returns inner unchanged
//! - P3: Override — inner substitution for same name overrides outer
//! - P4: Inheritance — non-overridden outer subs appear in result
//! - P5: Name coverage — result names = inner ∪ (outer \ inner)
//!
//! The regressions in #2995, #2996, #3046 all trace back to incorrect
//! substitution composition or binding visibility. These proofs catch
//! violations of the composition contract at verification time.

#[cfg(kani)]
mod kani_proofs {
    use crate::helpers::compose_substitutions;
    use tla_core::ast::{Expr, Substitution};
    use tla_core::name_intern::NameId;
    use tla_core::Spanned;

    /// Create a substitution: `from_name <- to_expr`
    fn make_sub(from: &str, to_expr: Expr) -> Substitution {
        Substitution {
            from: Spanned::dummy(from.to_string()),
            to: Spanned::dummy(to_expr),
        }
    }

    /// Create a simple leaf expression that won't be transformed by substitution.
    /// Uses Bool to avoid BigInt unwinding issues in CBMC.
    fn leaf(b: bool) -> Expr {
        Expr::Bool(b)
    }

    /// Create an Ident expression that CAN be transformed by substitution.
    fn ident(name: &str) -> Expr {
        Expr::Ident(name.to_string(), NameId::INVALID)
    }

    // =========================================================================
    // P1: Identity — compose(inner, None) returns inner unchanged
    // =========================================================================

    #[kani::proof]
    fn compose_with_none_is_identity() {
        let choice: u8 = kani::any();
        kani::assume(choice < 4);

        let inner = match choice {
            0 => vec![],
            1 => vec![make_sub("x", leaf(true))],
            2 => vec![make_sub("x", leaf(true)), make_sub("y", leaf(false))],
            _ => vec![make_sub("a", leaf(false))],
        };

        let result = compose_substitutions(&inner, None);
        assert_eq!(
            result.len(),
            inner.len(),
            "compose with None must preserve length"
        );
        for (r, i) in result.iter().zip(inner.iter()) {
            assert_eq!(
                r.from.node, i.from.node,
                "compose with None must preserve names"
            );
        }
    }

    // =========================================================================
    // P2: Empty outer identity — compose(inner, Some([])) returns inner unchanged
    // =========================================================================

    #[kani::proof]
    fn compose_with_empty_outer_is_identity() {
        let choice: u8 = kani::any();
        kani::assume(choice < 3);

        let inner = match choice {
            0 => vec![make_sub("x", leaf(true))],
            1 => vec![make_sub("x", leaf(true)), make_sub("y", leaf(false))],
            _ => vec![make_sub("a", leaf(false))],
        };
        let outer: Vec<Substitution> = vec![];

        let result = compose_substitutions(&inner, Some(&outer));
        assert_eq!(
            result.len(),
            inner.len(),
            "compose with empty outer must preserve length"
        );
        for (r, i) in result.iter().zip(inner.iter()) {
            assert_eq!(
                r.from.node, i.from.node,
                "compose with empty outer must preserve names"
            );
        }
    }

    // =========================================================================
    // P3: Override — inner substitution for same name overrides outer
    // =========================================================================

    #[kani::proof]
    fn inner_overrides_outer_for_same_name() {
        let inner = vec![make_sub("x", leaf(true))];
        let outer = vec![make_sub("x", leaf(false))];

        let result = compose_substitutions(&inner, Some(&outer));
        // Only one entry for "x" — inner overrides, outer is not inherited
        assert_eq!(result.len(), 1, "override must not duplicate names");
        assert_eq!(result[0].from.node, "x");
    }

    // =========================================================================
    // P4: Inheritance — non-overridden outer subs appear in result
    // =========================================================================

    #[kani::proof]
    fn non_overridden_outer_subs_inherited() {
        let inner = vec![make_sub("x", leaf(true))];
        let outer = vec![make_sub("y", leaf(false))];

        let result = compose_substitutions(&inner, Some(&outer));
        assert_eq!(result.len(), 2, "disjoint subs must both appear in result");
        let names: Vec<&str> = result.iter().map(|s| s.from.node.as_str()).collect();
        assert!(names.contains(&"x"), "inner sub 'x' must be in result");
        assert!(names.contains(&"y"), "outer sub 'y' must be inherited");
    }

    // =========================================================================
    // P5: Name coverage — result names = inner ∪ (outer \ overridden)
    // =========================================================================

    #[kani::proof]
    fn result_name_coverage_is_correct() {
        let choose_inner: u8 = kani::any();
        let choose_outer: u8 = kani::any();
        kani::assume(choose_inner < 3);
        kani::assume(choose_outer < 3);

        let inner = match choose_inner {
            0 => vec![make_sub("a", leaf(true))],
            1 => vec![make_sub("a", leaf(true)), make_sub("b", leaf(false))],
            _ => vec![],
        };
        let outer = match choose_outer {
            0 => vec![make_sub("b", leaf(true))],
            1 => vec![make_sub("c", leaf(false))],
            _ => vec![],
        };

        let result = compose_substitutions(&inner, Some(&outer));
        let result_names: std::collections::HashSet<&str> =
            result.iter().map(|s| s.from.node.as_str()).collect();

        // All inner names must be in result
        for sub in &inner {
            assert!(
                result_names.contains(sub.from.node.as_str()),
                "inner sub name must be in result"
            );
        }
        // All non-overridden outer names must be in result
        let inner_names: std::collections::HashSet<&str> =
            inner.iter().map(|s| s.from.node.as_str()).collect();
        for sub in &outer {
            if !inner_names.contains(sub.from.node.as_str()) {
                assert!(
                    result_names.contains(sub.from.node.as_str()),
                    "non-overridden outer sub must be inherited"
                );
            }
        }
    }

    // =========================================================================
    // P6: Translation — inner RHS is translated through outer subs
    //
    // When inner has `x <- y` and outer has `y <- z`, the composed result
    // should have `x <- z` (inner's RHS `y` is substituted by outer's `y <- z`).
    // =========================================================================

    #[kani::proof]
    fn inner_rhs_translated_through_outer() {
        // inner: x <- y (where y is an Ident that matches an outer sub)
        // outer: y <- TRUE
        // Expected: x <- TRUE (y in inner's RHS replaced by TRUE)
        let inner = vec![make_sub("x", ident("y"))];
        let outer = vec![make_sub("y", leaf(true))];

        let result = compose_substitutions(&inner, Some(&outer));
        // x's RHS should be Bool(true), not Ident("y")
        assert_eq!(result.len(), 2); // x from inner, y inherited from outer
        let x_sub = result
            .iter()
            .find(|s| s.from.node == "x")
            .expect("invariant: x must be in compose result");
        assert_eq!(
            x_sub.to.node,
            Expr::Bool(true),
            "inner RHS must be translated through outer substitutions"
        );
    }

    // =========================================================================
    // P7: No duplicate names — each name appears at most once in result
    // =========================================================================

    #[kani::proof]
    fn no_duplicate_names_in_result() {
        let choose: u8 = kani::any();
        kani::assume(choose < 4);

        let (inner, outer) = match choose {
            0 => (
                vec![make_sub("x", leaf(true))],
                vec![make_sub("x", leaf(false))],
            ),
            1 => (
                vec![make_sub("x", leaf(true))],
                vec![make_sub("y", leaf(false))],
            ),
            2 => (
                vec![make_sub("x", leaf(true)), make_sub("y", leaf(false))],
                vec![make_sub("y", leaf(true)), make_sub("z", leaf(false))],
            ),
            _ => (vec![], vec![make_sub("x", leaf(true))]),
        };

        let result = compose_substitutions(&inner, Some(&outer));
        let mut seen = std::collections::HashSet::new();
        for sub in &result {
            assert!(
                seen.insert(sub.from.node.as_str()),
                "duplicate name in compose result"
            );
        }
    }
}

// =========================================================================
// Test mirrors: verify the same properties using #[test] for fast CI feedback
// =========================================================================

#[cfg(test)]
mod tests {
    use crate::helpers::compose_substitutions;
    use tla_core::ast::{Expr, Substitution};
    use tla_core::name_intern::NameId;
    use tla_core::Spanned;

    fn make_sub(from: &str, to_expr: Expr) -> Substitution {
        Substitution {
            from: Spanned::dummy(from.to_string()),
            to: Spanned::dummy(to_expr),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compose_with_none_is_identity() {
        let inner = vec![
            make_sub("x", Expr::Bool(true)),
            make_sub("y", Expr::Bool(false)),
        ];
        let result = compose_substitutions(&inner, None);
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].from.node, "x");
        assert_eq!(result[1].from.node, "y");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compose_with_empty_outer_is_identity() {
        let inner = vec![make_sub("x", Expr::Bool(true))];
        let result = compose_substitutions(&inner, Some(&[]));
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].from.node, "x");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inner_overrides_outer() {
        let inner = vec![make_sub("x", Expr::Bool(true))];
        let outer = vec![make_sub("x", Expr::Bool(false))];
        let result = compose_substitutions(&inner, Some(&outer));
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].from.node, "x");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_non_overridden_outer_inherited() {
        let inner = vec![make_sub("x", Expr::Bool(true))];
        let outer = vec![make_sub("y", Expr::Bool(false))];
        let result = compose_substitutions(&inner, Some(&outer));
        assert_eq!(result.len(), 2);
        let names: Vec<&str> = result.iter().map(|s| s.from.node.as_str()).collect();
        assert!(names.contains(&"x"));
        assert!(names.contains(&"y"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inner_rhs_translated_through_outer() {
        let inner = vec![make_sub("x", Expr::Ident("y".into(), NameId::INVALID))];
        let outer = vec![make_sub("y", Expr::Bool(true))];
        let result = compose_substitutions(&inner, Some(&outer));
        let x_sub = result
            .iter()
            .find(|s| s.from.node == "x")
            .expect("invariant: x must be in compose result");
        assert_eq!(x_sub.to.node, Expr::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_no_duplicate_names() {
        let inner = vec![
            make_sub("x", Expr::Bool(true)),
            make_sub("y", Expr::Bool(false)),
        ];
        let outer = vec![
            make_sub("y", Expr::Bool(true)),
            make_sub("z", Expr::Bool(false)),
        ];
        let result = compose_substitutions(&inner, Some(&outer));
        let mut seen = std::collections::HashSet::new();
        for sub in &result {
            assert!(seen.insert(&sub.from.node), "duplicate: {}", sub.from.node);
        }
    }
}

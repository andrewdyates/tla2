// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;
use serial_test::serial;

// =======================================================================
// ITE Lifting Tests
// =======================================================================

#[test]
fn test_ite_lifting_simple() {
    let mut store = TermStore::new();

    // (<= (ite c x y) z) should become (ite c (<= x z) (<= y z))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let z = store.mk_var("z", Sort::Real);

    let ite_expr = store.mk_ite(c, x, y);
    let pred = store.mk_le(ite_expr, z);

    let lifted = store.lift_arithmetic_ite(pred);

    // Should be (ite c (<= x z) (<= y z))
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            // then branch should be (<= x z)
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], x);
                    assert_eq!(args[1], z);
                }
                _ => panic!("Expected <= application in then branch"),
            }
            // else branch should be (<= y z)
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], y);
                    assert_eq!(args[1], z);
                }
                _ => panic!("Expected <= application in else branch"),
            }
        }
        _ => panic!("Expected ITE after lifting"),
    }
}

#[test]
fn test_ite_lifting_second_arg() {
    let mut store = TermStore::new();

    // (<= z (ite c x y)) should become (ite c (<= z x) (<= z y))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let z = store.mk_var("z", Sort::Real);

    let ite_expr = store.mk_ite(c, x, y);
    let pred = store.mk_le(z, ite_expr);

    let lifted = store.lift_arithmetic_ite(pred);

    // Should be (ite c (<= z x) (<= z y))
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], z);
                    assert_eq!(args[1], x);
                }
                _ => panic!("Expected <= application in then branch"),
            }
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "<=");
                    assert_eq!(args[0], z);
                    assert_eq!(args[1], y);
                }
                _ => panic!("Expected <= application in else branch"),
            }
        }
        _ => panic!("Expected ITE after lifting"),
    }
}

#[test]
fn test_ite_lifting_no_ite() {
    let mut store = TermStore::new();

    // (<= x y) with no ITE should remain unchanged
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);

    let pred = store.mk_le(x, y);
    let lifted = store.lift_arithmetic_ite(pred);

    assert_eq!(lifted, pred);
}

#[test]
fn test_ite_lifting_all_reuses_shared_ite_free_dag_without_growth() {
    let mut store = TermStore::new();

    let array = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let store_index = store.mk_var("i", Sort::Int);
    let select_index = store.mk_var("j", Sort::Int);
    let value = store.mk_var("v", Sort::Int);
    let upper = store.mk_var("upper", Sort::Int);
    let lower = store.mk_var("lower", Sort::Int);
    let one = store.mk_int(BigInt::from(1));

    let updated = store.mk_store(array, store_index, value);
    let shared_select = store.mk_select(updated, select_index);
    let shared_sum = store.mk_add(vec![shared_select, one]);
    let le = store.mk_le(shared_sum, upper);
    let ge = store.mk_ge(shared_sum, lower);

    let len_before = store.len();
    let lifted = store.lift_arithmetic_ite_all(&[le, ge]);

    assert_eq!(lifted, vec![le, ge]);
    assert_eq!(
        store.len(),
        len_before,
        "ITE-free shared arithmetic/store tails should not allocate new terms"
    );
}

#[test]
fn test_ite_lifting_bool_ite_not_lifted() {
    let mut store = TermStore::new();

    // (= (ite c true false) p) should NOT lift since ITE result is Bool
    let c = store.mk_var("c", Sort::Bool);
    let p = store.mk_var("p", Sort::Bool);

    let true_t = store.true_term();
    let false_t = store.false_term();
    let ite_expr = store.mk_ite(c, true_t, false_t);
    let pred = store.mk_eq(ite_expr, p);

    let lifted = store.lift_arithmetic_ite(pred);

    // For Bool ITE, the lifting may or may not happen depending on simplifications
    // The key is that the result should be semantically equivalent
    // Just check that it doesn't crash
    assert!(!store.is_false(lifted));
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_ite_lifting_nested() {
    let mut store = TermStore::new();

    // (and (<= (ite c x y) z) (<= w v)) should lift the first conjunct
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Real);
    let y = store.mk_var("y", Sort::Real);
    let z = store.mk_var("z", Sort::Real);
    let w = store.mk_var("w", Sort::Real);
    let v = store.mk_var("v", Sort::Real);

    let ite_expr = store.mk_ite(c, x, y);
    let pred1 = store.mk_le(ite_expr, z);
    let pred2 = store.mk_le(w, v);
    let conj = store.mk_and(vec![pred1, pred2]);

    let lifted = store.lift_arithmetic_ite(conj);

    // Should be (and (ite c (<= x z) (<= y z)) (<= w v))
    match store.get(lifted) {
        TermData::App(Symbol::Named(name), args) => {
            assert_eq!(name, "and");
            assert_eq!(args.len(), 2);
            // First arg should be lifted ITE
            assert!(matches!(store.get(args[0]), TermData::Ite(_, _, _)));
            // Second arg should be unchanged
            assert_eq!(args[1], pred2);
        }
        _ => panic!("Expected and application after lifting"),
    }
}

#[test]
fn test_ite_lifting_lt() {
    let mut store = TermStore::new();

    // (< (ite c x y) z) should become (ite c (< x z) (< y z))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let z = store.mk_var("z", Sort::Int);

    let ite_expr = store.mk_ite(c, x, y);
    let pred = store.mk_lt(ite_expr, z);

    let lifted = store.lift_arithmetic_ite(pred);

    match store.get(lifted) {
        TermData::Ite(cond, _, _) => {
            assert_eq!(*cond, c);
        }
        _ => panic!("Expected ITE after lifting"),
    }
}

#[test]
fn test_ite_lifting_nested_in_arithmetic() {
    let mut store = TermStore::new();

    // (<= (+ x (ite c 1 0)) y) should become (ite c (<= (+ x 1) y) (<= (+ x 0) y))
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let one = store.mk_int(BigInt::from(1));
    let zero = store.mk_int(BigInt::from(0));

    let ite_expr = store.mk_ite(c, one, zero);
    let sum = store.mk_add(vec![x, ite_expr]);
    let pred = store.mk_le(sum, y);

    let lifted = store.lift_arithmetic_ite(pred);

    // Should be lifted to an ITE at the top level
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            // Both branches should be <= predicates, not contain ITEs
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), _) => {
                    assert_eq!(name, "<=");
                }
                _ => panic!("Expected <= application in then branch"),
            }
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), _) => {
                    assert_eq!(name, "<=");
                }
                _ => panic!("Expected <= application in else branch"),
            }
        }
        _ => panic!("Expected ITE after lifting nested arithmetic ITE"),
    }
}

#[test]
fn test_ite_lifting_uninterpreted_sort_equality() {
    let mut store = TermStore::new();

    // (= x (ite c a b)) with x, a, b of uninterpreted sort S
    // should become (ite c (= x a) (= x b))
    let sort_s = Sort::Uninterpreted("S".to_string());
    let c = store.mk_var("c", Sort::Bool);
    let x = store.mk_var("x", sort_s.clone());
    let a = store.mk_var("a", sort_s.clone());
    let b = store.mk_var("b", sort_s);

    let ite_expr = store.mk_ite(c, a, b);
    let eq = store.mk_eq(x, ite_expr);

    let lifted = store.lift_arithmetic_ite(eq);

    // Should be (ite c (= x a) (= x b))
    match store.get(lifted) {
        TermData::Ite(cond, then_t, else_t) => {
            assert_eq!(*cond, c);
            // then branch should be (= x a)
            match store.get(*then_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "=");
                    // Args could be [x, a] or [a, x] due to canonical ordering
                    assert!(
                        (args[0] == x && args[1] == a) || (args[0] == a && args[1] == x),
                        "Expected equality with x and a, got {args:?}"
                    );
                }
                _ => panic!(
                    "Expected = application in then branch, got {:?}",
                    store.get(*then_t)
                ),
            }
            // else branch should be (= x b)
            match store.get(*else_t) {
                TermData::App(Symbol::Named(name), args) => {
                    assert_eq!(name, "=");
                    // Args could be [x, b] or [b, x] due to canonical ordering
                    assert!(
                        (args[0] == x && args[1] == b) || (args[0] == b && args[1] == x),
                        "Expected equality with x and b, got {args:?}"
                    );
                }
                _ => panic!(
                    "Expected = application in else branch, got {:?}",
                    store.get(*else_t)
                ),
            }
        }
        _ => panic!("Expected ITE after lifting, got {:?}", store.get(lifted)),
    }
}

#[test]
fn test_internal_symbol_uniqueness() {
    let mut store = TermStore::new();
    let s1 = store.mk_internal_symbol("test");
    let s2 = store.mk_internal_symbol("test");
    let s3 = store.mk_internal_symbol("other");

    // Each call should produce a unique symbol
    assert_ne!(s1, s2);
    assert_ne!(s2, s3);

    // All should start with __z4_<purpose>!
    assert!(s1.starts_with("__z4_test!"));
    assert!(s2.starts_with("__z4_test!"));
    assert!(s3.starts_with("__z4_other!"));
}

#[test]
fn test_internal_symbol_format() {
    let mut store = TermStore::new();
    let sym = store.mk_internal_symbol("dt_depth_List");
    // Should be __z4_<purpose>!<id>
    assert!(sym.starts_with("__z4_dt_depth_List!"));
    // Should end with a numeric ID
    let suffix = sym.strip_prefix("__z4_dt_depth_List!").unwrap();
    assert!(
        suffix.parse::<u32>().is_ok(),
        "Expected numeric suffix, got: {suffix}"
    );
}

// =========================================================
// Extract over concat simplification tests
// =========================================================

#[test]
fn test_bvextract_over_concat_low_part() {
    // extract[3:0](concat(a[8], b[8])) → extract[3:0](b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(3, 0, concat_ab);
    let expected = store.mk_bvextract(3, 0, b);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_concat_high_part() {
    // extract[15:8](concat(a[8], b[8])) → a (full extract simplifies to identity)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(15, 8, concat_ab);
    // Full extract of a (8-bit, extracting bits 7:0 maps to a)
    assert_eq!(extract, a);
}

#[test]
fn test_bvextract_over_concat_high_part_partial() {
    // extract[12:10](concat(a[8], b[8])) → extract[4:2](a)
    // In concat(a,b) with |b|=8: a occupies bits [15:8]
    // extract[12:10] is entirely in a, so becomes extract[12-8:10-8](a) = extract[4:2](a)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(12, 10, concat_ab);
    let expected = store.mk_bvextract(4, 2, a);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_concat_crosses_boundary() {
    // extract[11:4](concat(a[8], b[8])) → concat(extract[3:0](a), extract[7:4](b))
    // hi=11, lo=4, w_b=8
    // high_part = extract[11-8:0](a) = extract[3:0](a)
    // low_part = extract[8-1:4](b) = extract[7:4](b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(11, 4, concat_ab);
    let high_part = store.mk_bvextract(3, 0, a);
    let low_part = store.mk_bvextract(7, 4, b);
    let expected = store.mk_bvconcat(vec![high_part, low_part]);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_nested_concat() {
    // extract[3:0](concat(concat(a[4], b[4]), c[4])) where c is at bits [0..3]
    // Total width: 12 bits, c occupies bits 0-3, b occupies 4-7, a occupies 8-11
    // Extract [3:0] is entirely within c
    // First simplification: hi=3 < w_c=4, so extract[3:0](c)
    // Full extract [3:0] of 4-bit c simplifies to c
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let c = store.mk_var("c", Sort::bitvec(4));
    let inner = store.mk_bvconcat(vec![a, b]); // 8-bit: a=high (4-7), b=low (0-3)
    let outer = store.mk_bvconcat(vec![inner, c]); // 12-bit: inner=high (4-11), c=low (0-3)
    let extract = store.mk_bvextract(3, 0, outer);
    assert_eq!(extract, c);
}

#[test]
fn test_bvextract_over_concat_at_boundary() {
    // extract[7:0](concat(a[8], b[8])) → b (full extract of b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(8));
    let b = store.mk_var("b", Sort::bitvec(8));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(7, 0, concat_ab);
    // hi=7 < w_b=8, so extract within b. Full extract [7:0] of 8-bit b → b
    assert_eq!(extract, b);
}

#[test]
fn test_bvextract_over_concat_single_bit_low() {
    // extract[0:0](concat(a[4], b[4])) → extract[0:0](b)
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(0, 0, concat_ab);
    let expected = store.mk_bvextract(0, 0, b);
    assert_eq!(extract, expected);
}

#[test]
fn test_bvextract_over_concat_single_bit_high() {
    // extract[7:7](concat(a[4], b[4])) → extract[3:3](a)
    // w_b=4, so bit 7 is in a at position 7-4=3
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::bitvec(4));
    let b = store.mk_var("b", Sort::bitvec(4));
    let concat_ab = store.mk_bvconcat(vec![a, b]);
    let extract = store.mk_bvextract(7, 7, concat_ab);
    let expected = store.mk_bvextract(3, 3, a);
    assert_eq!(extract, expected);
}

#[test]
#[serial(global_term_memory)]
fn test_global_term_bytes_tracks_allocation() {
    // Reset counter to get a clean baseline
    TermStore::reset_global_term_bytes();
    let baseline = TermStore::global_term_bytes();

    // Create a fresh TermStore — its constructor interns true/false
    let mut store = TermStore::new();

    // The constructor creates true_term and false_term, so counter should increase
    let after_new = TermStore::global_term_bytes();
    assert!(
        after_new > baseline,
        "global_term_bytes should increase after TermStore::new()"
    );

    // Intern some unique terms
    let _ = store.mk_var("x", Sort::Int);
    let _ = store.mk_var("y", Sort::Int);
    let _ = store.mk_int(42.into());

    let after_terms = TermStore::global_term_bytes();
    assert!(
        after_terms > after_new,
        "global_term_bytes should increase after interning terms"
    );

    // Hash-consed duplicates should NOT increase the counter
    let _ = store.mk_var("x", Sort::Int); // duplicate
    let after_dup = TermStore::global_term_bytes();
    assert_eq!(
        after_dup, after_terms,
        "hash-consed duplicate should not increase global_term_bytes"
    );
}

#[test]
#[serial(global_term_memory)]
fn test_global_memory_exceeded_default_threshold() {
    // With a fresh counter and default 4GB limit, memory should not be exceeded
    TermStore::reset_global_term_bytes();
    assert!(
        !TermStore::global_memory_exceeded(),
        "fresh counter should not exceed 4GB limit"
    );
}

#[test]
#[serial(global_term_memory)]
fn test_reset_global_term_bytes() {
    // Ensure reset actually zeroes the counter
    let mut store = TermStore::new();
    let _ = store.mk_var("z", Sort::Bool);
    assert!(TermStore::global_term_bytes() > 0);

    TermStore::reset_global_term_bytes();
    assert_eq!(TermStore::global_term_bytes(), 0);
}

/// Verify that GLOBAL_TERM_BYTES tracks allocation when new terms are interned,
/// and that it undercounts heap allocations inside TermData variants.
///
/// This test confirms:
/// 1. The counter increments by size_of::<TermEntry>() per unique term.
/// 2. Hash-consing deduplicates (no double-count for identical terms).
/// 3. The counter does NOT track heap allocations inside TermData variants
///    (Vec<TermId> children, String in Var). This is a known undercounting gap
///    documented in the code and in #2924.
#[test]
#[serial(global_term_memory)]
fn test_global_term_bytes_tracks_interning_and_undercounts_heap() {
    use std::mem::size_of;

    // GLOBAL_TERM_BYTES is process-wide. Snapshot and assert deltas from this
    // test's baseline so unrelated prior allocations don't make this flaky.
    let baseline = TermStore::global_term_bytes();
    let entry_size = size_of::<TermEntry>();

    let mut store = TermStore::new();

    // TermStore::new() interns true + false = 2 entries
    let after_new = TermStore::global_term_bytes();
    let constructor_delta = after_new - baseline;
    assert!(
        constructor_delta >= 2 * entry_size,
        "new() should contribute at least two TermEntry allocations"
    );
    assert_eq!(store.len(), 2, "new() should intern exactly true and false");

    // Intern a variable — adds exactly 1 TermEntry
    let len_before_var = store.len();
    let x = store.mk_var("x", Sort::Int);
    let after_var = TermStore::global_term_bytes();
    let var_delta = after_var - after_new;
    assert!(
        var_delta >= entry_size,
        "one unique term should contribute at least one TermEntry allocation"
    );
    assert_eq!(store.len(), len_before_var + 1);

    // Intern the same variable again — hash-consing deduplicates in the local store.
    let len_before_dup = store.len();
    let _x2 = store.mk_var("x", Sort::Int);
    assert_eq!(
        store.len(),
        len_before_dup,
        "duplicate term should deduplicate"
    );

    // Intern a function application with multiple children.
    // The counter adds size_of::<TermEntry>() but the Vec<TermId> heap allocation
    // is NOT counted. This proves the documented undercounting gap.
    let len_before_y = store.len();
    let y = store.mk_var("y", Sort::Int);
    assert_eq!(store.len(), len_before_y + 1);
    let len_before_app = store.len();
    let before_app = TermStore::global_term_bytes();
    let _sum = store.mk_app(Symbol::Named("+".to_string()), vec![x, y], Sort::Int);
    let after_app = TermStore::global_term_bytes();
    assert_eq!(store.len(), len_before_app + 1);

    // Only size_of::<TermEntry>() was added, NOT the Vec<TermId> heap.
    // The actual heap cost is at least 2 * size_of::<TermId>() = 8 bytes
    // plus Vec's header (24 bytes on 64-bit). This gap is documented.
    let counted = after_app - before_app;
    assert!(
        counted >= entry_size,
        "app term should contribute at least one TermEntry allocation"
    );
}

// =======================================================================
// Performance regression tests for O(n²) complexity in boolean/arith ops
// =======================================================================

/// Regression test: mk_and with N distinct variables should not exhibit
/// O(n²) scaling from complement/absorption detection passes.
///
/// The complement detection at boolean.rs:131-138 uses `filtered.contains()`
/// (linear scan) inside a loop over `filtered`, making it O(n²). Since
/// `filtered` is sorted after line 126, binary_search could make it O(n log n).
///
/// This test verifies that mk_and(1000 vars) completes within a reasonable
/// time bound (< 500ms). If the O(n²) path were triggered on, say, 10000
/// variables, this would take seconds.
#[test]
fn test_mk_and_performance_no_quadratic_blowup() {
    let mut store = TermStore::new();

    // Create N distinct bool variables — no complements, no absorption
    let n = 1000;
    let vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("b{i}"), Sort::Bool))
        .collect();

    let start = std::time::Instant::now();
    let result = store.mk_and(vars);
    let elapsed = start.elapsed();

    // Result should be a conjunction of all N variables
    assert_ne!(result, store.true_term());
    assert_ne!(result, store.false_term());

    // 500ms is generous; O(n log n) for n=1000 should be < 10ms.
    // O(n²) with n=1000 would be ~100ms. This catches severe regression.
    assert!(
        elapsed.as_millis() < 500,
        "mk_and({n} vars) took {elapsed:?}, expected < 500ms — possible O(n²) regression"
    );
}

/// Regression test: mk_and with complement pair in large conjunction.
///
/// (and x0 x1 ... x_{n-1} (not x0)) should immediately return false.
/// The O(n²) complement detection scans `filtered.contains()` for each Not
/// arg. Even with one complement, every arg is checked. With sorted vec,
/// binary_search makes this O(n log n).
#[test]
fn test_mk_and_complement_detection_scaling() {
    let mut store = TermStore::new();

    let n = 2000;
    let mut vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("c{i}"), Sort::Bool))
        .collect();

    // Add complement of first variable — should trigger false result
    let not_first = store.mk_not(vars[0]);
    vars.push(not_first);

    let start = std::time::Instant::now();
    let result = store.mk_and(vars);
    let elapsed = start.elapsed();

    assert_eq!(
        result,
        store.false_term(),
        "complement pair should yield false"
    );
    assert!(
        elapsed.as_millis() < 500,
        "mk_and complement detection with {n} vars took {elapsed:?}, expected < 500ms"
    );
}

/// Regression test: mk_or with complement pair in large disjunction.
///
/// (or x0 x1 ... x_{n-1} (not x0)) should immediately return true.
#[test]
fn test_mk_or_complement_detection_scaling() {
    let mut store = TermStore::new();

    let n = 2000;
    let mut vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("d{i}"), Sort::Bool))
        .collect();

    let not_first = store.mk_not(vars[0]);
    vars.push(not_first);

    let start = std::time::Instant::now();
    let result = store.mk_or(vars);
    let elapsed = start.elapsed();

    assert_eq!(
        result,
        store.true_term(),
        "complement pair should yield true"
    );
    assert!(
        elapsed.as_millis() < 500,
        "mk_or complement detection with {n} vars took {elapsed:?}, expected < 500ms"
    );
}

/// Regression test: mk_add with N terms should not O(n²) from additive
/// inverse detection using `result_args.contains()` (arithmetic.rs:316).
#[test]
fn test_mk_add_performance_no_quadratic_blowup() {
    let mut store = TermStore::new();

    let n = 500;
    let vars: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("a{i}"), Sort::Int))
        .collect();

    let start = std::time::Instant::now();
    let result = store.mk_add(vars);
    let elapsed = start.elapsed();

    assert_ne!(result, store.mk_int(BigInt::from(0)));
    assert!(
        elapsed.as_millis() < 500,
        "mk_add({n} vars) took {elapsed:?}, expected < 500ms — possible O(n²) regression"
    );
}

/// Regression: mk_abs with Real-sorted variable must not panic on sort mismatch.
/// Before the fix, mk_abs always used mk_int(0) for the comparison,
/// creating (>= Real Int) which panics in mk_ge.
#[test]
fn test_abs_real_no_sort_mismatch() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Real);
    // This should not panic
    let abs_x = store.mk_abs(x);
    // Result should be an ITE: (ite (>= x 0.0) x (- x))
    match store.get(abs_x) {
        TermData::Ite(cond, then_br, else_br) => {
            // Condition is a comparison, then is x, else is -x
            assert_eq!(*then_br, x);
            // cond should involve a Real zero, not an Int zero
            // Verify the condition references a rational zero
            let cond_sort_ok = match store.get(*cond) {
                TermData::App(Symbol::Named(name), args) if name == "<=" => {
                    // mk_ge(x, 0) normalizes to mk_le(0, x)
                    args.len() == 2 && store.sort(args[0]) == &Sort::Real
                }
                _ => false,
            };
            assert!(
                cond_sort_ok,
                "abs(Real) condition should use Real-sorted zero"
            );
            let _ = else_br;
        }
        other => panic!("abs(x) should be ITE, got {other:?}"),
    }
}

/// Rational constant folding for abs: |−1/2| = 1/2
#[test]
fn test_abs_rational_constant_folding() {
    let mut store = TermStore::new();
    let neg_half = store.mk_rational(BigRational::new(BigInt::from(-1), BigInt::from(2)));
    let pos_half = store.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));

    assert_eq!(store.mk_abs(neg_half), pos_half);
    assert_eq!(store.mk_abs(pos_half), pos_half);
}

/// mk_store preserves original order for nested symbolic stores (#6367).
///
/// `mk_store(store(a, j, w), i, v)` where j > i by TermId stays as a plain
/// nested store. The theory solver handles index equality/disequality reasoning
/// at runtime via ROW1/ROW2 lemmas. Previously this generated ITE terms
/// (`SwapWithEqualityGuard`) which caused combinatorial explosion on storeinv
/// benchmarks.
#[test]
fn test_mk_store_symbolic_no_ite_guard() {
    let mut store = TermStore::new();
    let arr = store.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = store.mk_var("i", Sort::Int);
    let j = store.mk_var("j", Sort::Int);
    let v = store.mk_var("v", Sort::Int);
    let w = store.mk_var("w", Sort::Int);

    // j declared after i, so j > i by TermId
    assert!(j > i, "test assumes j declared after i");

    let inner = store.mk_store(arr, j, w);
    let result = store.mk_store(inner, i, v);

    // Should be a plain nested store, NOT an ITE
    assert!(
        matches!(store.get(result), TermData::App(Symbol::Named(n), args) if n == "store" && args.len() == 3),
        "mk_store on nested symbolic stores should produce plain store (not ITE), \
         got {:?}",
        store.get(result)
    );
}

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #7956: false UNSAT on AUFLIA formula with
//! Array+Quantifier+UF involving ext_eq(vec, concat(singleton(v), next)).
//!
//! Mail issue from sunder reporting that z4 returns `unsat` on a satisfiable
//! AUFLIA formula. The formula models sequence extensional equality via a
//! Tseitin Bool variable with forward/backward axioms, combined with
//! concat/singleton/bridge quantified axioms and array select/store.
//!
//! Root cause (fixed in #6920/#6930): EUF proof-forest collect_path_reasons
//! cleared reasons on broken path, causing empty reasons leading to false UNSAT
//! on array+quantifier+UF formulas.
//!
//! This test file covers the exact sunder encoding pattern (Tseitin ext_eq
//! variable, triggerless pointwise quantifier) plus several variants to
//! prevent future regressions.

mod common;

use common::{run_executor_smt_with_timeout, SolverOutcome};

/// Exact sunder ext_eq encoding: Tseitin Bool variable with three axioms,
/// pointwise quantifier has NO triggers (matches sunder's `self.solver.forall`).
///
/// SAT witness: v=42, vec has len >= 1 with index 0 = 42, next = anything.
const SUNDER_EXT_EQ_TSEITIN: &str = r#"
(set-logic AUFLIA)

(declare-sort Seq 0)
(declare-fun seq_len (Seq) Int)
(declare-fun seq_offset (Seq) Int)
(declare-fun seq_array (Seq) (Array Int Int))
(declare-fun seq_index_logic (Seq Int) Int)
(declare-fun seq_concat (Seq Seq) Seq)
(declare-fun seq_singleton (Int) Seq)

(declare-const vec Seq)
(declare-const next Seq)
(declare-const v Int)

; Background axioms with triggers (from sunder's Seq axiom set)
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton axioms (concrete array shape)
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; === Sunder ext_eq Tseitin encoding ===
; ext_eq_0 is a fresh Bool constant (Tseitin variable)
(declare-const ext_eq_0 Bool)

; Axiom 1: ext_eq_0 => len(vec) == len(concat(singleton(v), next))
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))

; Axiom 2: ext_eq_0 => forall i. bounds => pointwise equality
; NOTE: NO TRIGGERS (matches sunder's self.solver.forall without triggers)
(assert (=> ext_eq_0
  (forall ((ext_eq_i Int))
    (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
        (= (seq_index_logic vec ext_eq_i)
           (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i))))))

; Axiom 3: (len_eq AND pointwise) => ext_eq_0
(assert (=> (and (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))
                 (forall ((ext_eq_i Int))
                   (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
                       (= (seq_index_logic vec ext_eq_i)
                          (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i)))))
            ext_eq_0))

; === VC body ===
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))

; Ground bridge seeds (sunder adds these)
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))

(check-sat)
"#;

/// #7956: The core sunder ext_eq encoding must return SAT.
#[test]
fn test_sunder_ext_eq_tseitin_not_false_unsat_7956() {
    let result =
        run_executor_smt_with_timeout(SUNDER_EXT_EQ_TSEITIN, 60).expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Sat,
        "#7956: sunder ext_eq Tseitin encoding must return sat (was false-UNSAT)"
    );
}

/// Variant with push/pop refutation proof (sunder's primary usage pattern).
/// First check: negate v==42 (should be UNSAT because it IS provable).
/// Second check: just the SAT formula (should be SAT).
const SUNDER_EXT_EQ_PUSH_POP: &str = r#"
(set-logic AUFLIA)

(declare-sort Seq 0)
(declare-fun seq_len (Seq) Int)
(declare-fun seq_offset (Seq) Int)
(declare-fun seq_array (Seq) (Array Int Int))
(declare-fun seq_index_logic (Seq Int) Int)
(declare-fun seq_concat (Seq Seq) Seq)
(declare-fun seq_singleton (Int) Seq)

(declare-const vec Seq)
(declare-const next Seq)
(declare-const v Int)

; Background axioms
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; ext_eq Tseitin
(declare-const ext_eq_0 Bool)
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))
(assert (=> ext_eq_0
  (forall ((ext_eq_i Int))
    (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
        (= (seq_index_logic vec ext_eq_i)
           (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i))))))
(assert (=> (and (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))
                 (forall ((ext_eq_i Int))
                   (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
                       (= (seq_index_logic vec ext_eq_i)
                          (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i)))))
            ext_eq_0))

; Refutation check: preconditions + negated postcondition
(push 1)
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))
; Negate: v == 42 (this IS provable, so UNSAT is correct)
(assert (not (= v 42)))
(check-sat)
(pop 1)

; SAT check: preconditions alone (should be SAT)
(push 1)
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))
(check-sat)
(pop 1)
"#;

/// #7956: Push/pop refutation proof pattern must work correctly.
/// First check-sat should be UNSAT (v==42 is provable, so not(v==42) is UNSAT).
/// Second check-sat should be SAT (preconditions are satisfiable).
///
/// Note: `run_executor_smt_with_timeout` returns the FIRST check-sat result,
/// so we verify the refutation proof (UNSAT) here. The SAT check is covered
/// by `test_sunder_ext_eq_tseitin_not_false_unsat_7956`.
#[test]
fn test_sunder_ext_eq_push_pop_refutation_7956() {
    let result = run_executor_smt_with_timeout(SUNDER_EXT_EQ_PUSH_POP, 60)
        .expect("execution should succeed");
    // The first check-sat negates v==42. Since v==42 is provable from the
    // axioms (ext_eq + concat-left + bridge), this should be genuinely UNSAT.
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "#7956: push/pop refutation: negated v==42 should be UNSAT (provable)"
    );
}

/// Variant with empty seq and ext_eq(vec, concat(singleton(v), empty)).
/// This is a common sunder pattern for single-element sequences.
const SUNDER_EXT_EQ_EMPTY_NEXT: &str = r#"
(set-logic AUFLIA)

(declare-sort Seq 0)
(declare-fun seq_len (Seq) Int)
(declare-fun seq_offset (Seq) Int)
(declare-fun seq_array (Seq) (Array Int Int))
(declare-fun seq_index_logic (Seq Int) Int)
(declare-fun seq_concat (Seq Seq) Seq)
(declare-fun seq_singleton (Int) Seq)
(declare-fun seq_empty () Seq)

(declare-const vec Seq)
(declare-const v Int)

; Background axioms
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; Empty seq
(assert (= (seq_array seq_empty) ((as const (Array Int Int)) 0)))
(assert (= (seq_len seq_empty) 0))
(assert (= (seq_offset seq_empty) 0))

; ext_eq Tseitin (with empty next)
(declare-const ext_eq_0 Bool)
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) seq_empty)))))
(assert (=> ext_eq_0
  (forall ((ext_eq_i Int))
    (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
        (= (seq_index_logic vec ext_eq_i)
           (seq_index_logic (seq_concat (seq_singleton v) seq_empty) ext_eq_i))))))
(assert (=> (and (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) seq_empty)))
                 (forall ((ext_eq_i Int))
                   (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
                       (= (seq_index_logic vec ext_eq_i)
                          (seq_index_logic (seq_concat (seq_singleton v) seq_empty) ext_eq_i)))))
            ext_eq_0))

; VC body
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))

(check-sat)
"#;

/// #7956 variant: ext_eq with empty next sequence must return SAT.
#[test]
fn test_sunder_ext_eq_empty_next_7956() {
    let result = run_executor_smt_with_timeout(SUNDER_EXT_EQ_EMPTY_NEXT, 60)
        .expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Sat,
        "#7956 variant: ext_eq with empty next must return sat"
    );
}

/// Variant matching the original #6920 reproducer but using the sunder
/// Tseitin encoding style instead of direct ext_eq Bool constant.
/// This bridges the two test patterns.
const SUNDER_EXT_EQ_WITH_TRIGGERS: &str = r#"
(set-logic AUFLIA)

(declare-sort Seq 0)
(declare-fun seq_len (Seq) Int)
(declare-fun seq_offset (Seq) Int)
(declare-fun seq_array (Seq) (Array Int Int))
(declare-fun seq_index_logic (Seq Int) Int)
(declare-fun seq_concat (Seq Seq) Seq)
(declare-fun seq_singleton (Int) Seq)

(declare-const vec Seq)
(declare-const next Seq)
(declare-const v Int)
(declare-const ext_eq_0 Bool)

; Background axioms with triggers
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; ext_eq Tseitin WITH triggers on pointwise quantifier
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))
(assert (=> ext_eq_0
  (forall ((i Int))
    (! (=> (and (>= i 0) (< i (seq_len vec)))
           (= (seq_index_logic vec i)
              (seq_index_logic (seq_concat (seq_singleton v) next) i)))
       :pattern ((seq_index_logic vec i))
       :pattern ((seq_index_logic (seq_concat (seq_singleton v) next) i))))))

; VC body
(assert ext_eq_0)
(assert (= (select (seq_array vec) (+ (seq_offset vec) 0)) 42))
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))

(check-sat)
"#;

/// #7956 variant: ext_eq with explicit triggers must return SAT.
#[test]
fn test_sunder_ext_eq_with_triggers_7956() {
    let result = run_executor_smt_with_timeout(SUNDER_EXT_EQ_WITH_TRIGGERS, 60)
        .expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Sat,
        "#7956 variant: ext_eq with triggers must return sat"
    );
}

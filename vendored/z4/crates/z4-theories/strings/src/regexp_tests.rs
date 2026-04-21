// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use z4_core::term::Symbol;
use z4_core::Sort;
use z4_core::TheoryResult;

// ── Helper constructors (tests have mutable TermStore) ─────────────

fn mk_re_none(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named("re.none"), vec![], Sort::RegLan)
}

fn mk_re_all(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named("re.all"), vec![], Sort::RegLan)
}

fn mk_str_to_re(terms: &mut TermStore, s: &str) -> TermId {
    let str_const = terms.mk_string(s.to_string());
    terms.mk_app(Symbol::named("str.to_re"), vec![str_const], Sort::RegLan)
}

fn mk_re_concat(terms: &mut TermStore, children: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("re.++"), children, Sort::RegLan)
}

fn mk_re_union(terms: &mut TermStore, children: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("re.union"), children, Sort::RegLan)
}

fn mk_re_inter(terms: &mut TermStore, children: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("re.inter"), children, Sort::RegLan)
}

fn mk_re_star(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.*"), vec![child], Sort::RegLan)
}

fn mk_re_plus(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.+"), vec![child], Sort::RegLan)
}

fn mk_re_opt(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.opt"), vec![child], Sort::RegLan)
}

fn mk_re_comp(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.comp"), vec![child], Sort::RegLan)
}

fn mk_re_diff(terms: &mut TermStore, r1: TermId, r2: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.diff"), vec![r1, r2], Sort::RegLan)
}

fn mk_re_range(terms: &mut TermStore, lo: &str, hi: &str) -> TermId {
    let lo_t = terms.mk_string(lo.to_string());
    let hi_t = terms.mk_string(hi.to_string());
    terms.mk_app(Symbol::named("re.range"), vec![lo_t, hi_t], Sort::RegLan)
}

fn mk_re_allchar(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named("re.allchar"), vec![], Sort::RegLan)
}

fn mk_re_loop(terms: &mut TermStore, child: TermId, lo: u32, hi: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("re.loop", vec![lo, hi]),
        vec![child],
        Sort::RegLan,
    )
}

// ── delta tests ────────────────────────────────────────────────────

#[test]
fn delta_re_none_is_false() {
    let mut terms = TermStore::new();
    let r = mk_re_none(&mut terms);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_allchar_is_false() {
    let mut terms = TermStore::new();
    let r = mk_re_allchar(&mut terms);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_all_is_true() {
    let mut terms = TermStore::new();
    let r = mk_re_all(&mut terms);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_str_to_re_empty_is_true() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "");
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_str_to_re_nonempty_is_false() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "a");
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_star_is_true() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a");
    let r = mk_re_star(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_re_plus_nonempty_is_false() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a");
    let r = mk_re_plus(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_opt_is_true() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a");
    let r = mk_re_opt(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_re_concat_all_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "");
    let inner = mk_str_to_re(&mut terms, "a");
    let r2 = mk_re_star(&mut terms, inner);
    let concat = mk_re_concat(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, concat), Some(true));
}

#[test]
fn delta_re_concat_one_not_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "a");
    let inner = mk_str_to_re(&mut terms, "b");
    let r2 = mk_re_star(&mut terms, inner);
    let concat = mk_re_concat(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, concat), Some(false));
}

#[test]
fn delta_re_union_one_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "a");
    let r2 = mk_str_to_re(&mut terms, "");
    let union = mk_re_union(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, union), Some(true));
}

#[test]
fn delta_re_union_none_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "a");
    let r2 = mk_str_to_re(&mut terms, "b");
    let union = mk_re_union(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, union), Some(false));
}

#[test]
fn delta_re_comp_flips() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a"); // not nullable
    let comp = mk_re_comp(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, comp), Some(true));

    let inner2 = mk_str_to_re(&mut terms, ""); // nullable
    let comp2 = mk_re_comp(&mut terms, inner2);
    assert_eq!(RegExpSolver::delta(&terms, comp2), Some(false));
}

#[test]
fn delta_re_diff() {
    let mut terms = TermStore::new();
    let all = mk_re_all(&mut terms);
    let inner = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, inner);
    // diff(re.all, re.*(str.to_re("a"))): both nullable, so false
    let diff = mk_re_diff(&mut terms, all, star);
    assert_eq!(RegExpSolver::delta(&terms, diff), Some(false));
}

// ── evaluate tests ─────────────────────────────────────────────────

#[test]
fn eval_re_none() {
    let mut terms = TermStore::new();
    let r = mk_re_none(&mut terms);
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(false));
}

#[test]
fn eval_re_all() {
    let mut terms = TermStore::new();
    let r = mk_re_all(&mut terms);
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "anything", r), Some(true));
}

#[test]
fn eval_allchar() {
    let mut terms = TermStore::new();
    let r = mk_re_allchar(&mut terms);
    assert_eq!(RegExpSolver::evaluate(&terms, "x", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", r), Some(false));
}

#[test]
fn eval_range() {
    let mut terms = TermStore::new();
    let r = mk_re_range(&mut terms, "a", "z");
    assert_eq!(RegExpSolver::evaluate(&terms, "m", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "z", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "A", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", r), Some(false));
}

#[test]
fn eval_str_to_re() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "hello");
    assert_eq!(RegExpSolver::evaluate(&terms, "hello", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "hell", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "helloo", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
}

#[test]
fn eval_str_to_re_empty() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "");
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(false));
}

#[test]
fn eval_concat() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let concat = mk_re_concat(&mut terms, vec![a, b]);
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ba", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "", concat), Some(false));
}

#[test]
fn eval_union() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let union = mk_re_union(&mut terms, vec![a, b]);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", union), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", union), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "c", union), Some(false));
}

#[test]
fn eval_inter() {
    let mut terms = TermStore::new();
    // re.inter(re.*(a), re.*(a|b)) — both match "a" and "aaa", first doesn't match "b"
    let a = mk_str_to_re(&mut terms, "a");
    let star_a = mk_re_star(&mut terms, a);
    let a2 = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let union_ab = mk_re_union(&mut terms, vec![a2, b]);
    let star_ab = mk_re_star(&mut terms, union_ab);
    let inter = mk_re_inter(&mut terms, vec![star_a, star_ab]);
    assert_eq!(RegExpSolver::evaluate(&terms, "", inter), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", inter), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", inter), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", inter), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", inter), Some(false));
}

#[test]
fn eval_star_empty_string() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "", star), Some(true));
}

#[test]
fn eval_star_single() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", star), Some(true));
}

#[test]
fn eval_star_repeated() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", star), Some(true));
}

#[test]
fn eval_star_non_matching() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "b", star), Some(false));
}

#[test]
fn eval_star_multi_char_pattern() {
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let star = mk_re_star(&mut terms, ab);
    assert_eq!(RegExpSolver::evaluate(&terms, "", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "abab", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", star), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "aba", star), Some(false));
}

#[test]
fn eval_plus() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let plus = mk_re_plus(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "", plus), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", plus), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", plus), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", plus), Some(false));
}

#[test]
fn eval_opt() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let opt = mk_re_opt(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "", opt), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", opt), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aa", opt), Some(false));
}

#[test]
fn eval_comp() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let comp = mk_re_comp(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", comp), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", comp), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "", comp), Some(true));
}

#[test]
fn eval_diff() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let union_ab = mk_re_union(&mut terms, vec![a, b]);
    let b2 = mk_str_to_re(&mut terms, "b");
    let diff = mk_re_diff(&mut terms, union_ab, b2);
    // (a|b) \ b = a
    assert_eq!(RegExpSolver::evaluate(&terms, "a", diff), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", diff), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "c", diff), Some(false));
}

// ── Complex regex evaluation ───────────────────────────────────────

#[test]
fn eval_star_a_then_b() {
    // (re.++ (re.* (str.to_re "a")) (str.to_re "b"))
    // Matches: "b", "ab", "aab", "aaab", ...
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let star_a = mk_re_star(&mut terms, a);
    let concat = mk_re_concat(&mut terms, vec![star_a, b]);

    assert_eq!(RegExpSolver::evaluate(&terms, "b", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aab", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ba", concat), Some(false));
}

#[test]
fn eval_digit_star() {
    // (re.* (re.range "0" "9"))
    let mut terms = TermStore::new();
    let digits = mk_re_range(&mut terms, "0", "9");
    let star = mk_re_star(&mut terms, digits);
    assert_eq!(RegExpSolver::evaluate(&terms, "", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "42", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "abc", star), Some(false));
}

#[test]
fn eval_email_like_pattern() {
    // Simplified: (re.++ (re.+ (re.range "a" "z")) (str.to_re "@") (re.+ (re.range "a" "z")))
    let mut terms = TermStore::new();
    let az = mk_re_range(&mut terms, "a", "z");
    let user = mk_re_plus(&mut terms, az);
    let at = mk_str_to_re(&mut terms, "@");
    let az2 = mk_re_range(&mut terms, "a", "z");
    let domain = mk_re_plus(&mut terms, az2);
    let email = mk_re_concat(&mut terms, vec![user, at, domain]);

    assert_eq!(RegExpSolver::evaluate(&terms, "a@b", email), Some(true));
    assert_eq!(
        RegExpSolver::evaluate(&terms, "user@host", email),
        Some(true)
    );
    assert_eq!(RegExpSolver::evaluate(&terms, "@host", email), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "user@", email), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "user", email), Some(false));
}

// ── check() integration tests ──────────────────────────────────────

#[test]
fn check_positive_membership_true_is_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let a = mk_str_to_re(&mut terms, "hello");
    let star = mk_re_star(&mut terms, a);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, star], Sort::Bool);
    let eq = terms.mk_eq(x, hello);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, eq, true);
    // Merge x with "hello" so resolve_string finds it.
    state.register_term(&terms, x);
    state.register_term(&terms, hello);
    let _ = state.merge(x, hello, TheoryLit::new(eq, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    // "hello" matches (re.* (str.to_re "hello")), positive assertion.
    // No conflict expected.
    assert!(!conflict, "positive membership true should not conflict");
}

#[test]
fn check_positive_membership_false_is_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let goodbye = terms.mk_string("goodbye".to_string());
    let a = mk_str_to_re(&mut terms, "hello");
    let star = mk_re_star(&mut terms, a);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, star], Sort::Bool);
    let eq = terms.mk_eq(x, goodbye);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, eq, true);
    state.register_term(&terms, x);
    state.register_term(&terms, goodbye);
    let _ = state.merge(x, goodbye, TheoryLit::new(eq, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    // "goodbye" does NOT match (re.* (str.to_re "hello")), but asserted positively.
    assert!(conflict, "positive membership false should conflict");
}

#[test]
fn check_negative_membership_true_is_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let a = mk_str_to_re(&mut terms, "hello");
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, a], Sort::Bool);
    let eq = terms.mk_eq(x, hello);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, false); // NOT in_re
    state.assert_literal(&terms, eq, true);
    state.register_term(&terms, x);
    state.register_term(&terms, hello);
    let _ = state.merge(x, hello, TheoryLit::new(eq, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    // "hello" matches (str.to_re "hello"), but asserted negatively.
    assert!(
        conflict,
        "negative membership of matching string should conflict"
    );
}

#[test]
fn check_conflict_explanation_excludes_unrelated_assertion() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let goodbye = terms.mk_string("goodbye".to_string());
    let unrelated = terms.mk_string("unrelated".to_string());
    let re_hello = mk_str_to_re(&mut terms, "hello");
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re_hello], Sort::Bool);
    let eq_x_goodbye = terms.mk_eq(x, goodbye);
    let eq_y_unrelated = terms.mk_eq(y, unrelated);

    let mut state = SolverState::new();
    // Include an unrelated fact to ensure regex conflicts stay targeted.
    state.assert_literal(&terms, eq_y_unrelated, true);
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, eq_x_goodbye, true);
    state.register_term(&terms, x);
    state.register_term(&terms, goodbye);
    let _ = state.merge(x, goodbye, TheoryLit::new(eq_x_goodbye, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);
    assert!(
        conflict,
        "x=\"goodbye\" does not satisfy str.in_re(x, \"hello\")"
    );

    let in_re_lit = TheoryLit::new(in_re, true);
    let eq_lit = TheoryLit::new(eq_x_goodbye, true);
    let unrelated_lit = TheoryLit::new(eq_y_unrelated, true);
    match infer.to_theory_result() {
        TheoryResult::Unsat(lits) => {
            assert!(
                lits.contains(&in_re_lit),
                "must include membership assertion"
            );
            assert!(
                lits.contains(&eq_lit),
                "must include x=\"goodbye\" assertion"
            );
            assert!(
                !lits.contains(&unrelated_lit),
                "must not include unrelated assertion in regex conflict explanation"
            );
            assert!(
                lits.len() <= 3,
                "targeted regex explanation unexpectedly large: {lits:?}"
            );
        }
        other => panic!("expected Unsat conflict, got {other:?}"),
    }
}

#[test]
fn check_unresolved_string_marks_incomplete() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, star], Sort::Bool);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.register_term(&terms, x);

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    assert!(!conflict, "unresolved string should not conflict");
    assert!(
        solver.is_incomplete(),
        "unresolved string should mark incomplete"
    );
}

// ── re.loop tests ─────────────────────────────────────────────────

#[test]
fn eval_loop_exact_match() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 3, 3);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", r), Some(true));
}

#[test]
fn eval_loop_too_few() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 2, 5);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(false));
}

#[test]
fn eval_loop_too_many() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 2, 3);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaaa", r), Some(false));
}

#[test]
fn eval_loop_zero_min_empty() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 0, 3);
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(true));
}

#[test]
fn eval_loop_multi_char_pattern() {
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_loop(&mut terms, ab, 2, 4);
    assert_eq!(RegExpSolver::evaluate(&terms, "abab", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ababab", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", r), Some(false));
}

#[test]
fn eval_loop_lo_gt_hi_is_false() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 5, 2);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", r), Some(false));
}

#[test]
fn delta_re_loop_zero_min_is_nullable() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 0, 5);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_re_loop_nonzero_min_nonempty_is_not_nullable() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 1, 5);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_loop_nonzero_min_nullable_inner() {
    let mut terms = TermStore::new();
    let empty = mk_str_to_re(&mut terms, "");
    let r = mk_re_loop(&mut terms, empty, 2, 5);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

// ── find_first_match tests ──────────────────────────────────────────

#[test]
fn find_first_match_literal_at_start() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "ab");
    match RegExpSolver::find_first_match(&terms, "abcdef", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 2);
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_literal_in_middle() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "cd");
    match RegExpSolver::find_first_match(&terms, "abcdef", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 2);
            assert_eq!(end, 4);
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_no_match() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "xyz");
    assert!(matches!(
        RegExpSolver::find_first_match(&terms, "abcdef", r),
        MatchResult::NoMatch
    ));
}

#[test]
fn find_first_match_empty_regex_matches_at_start() {
    let mut terms = TermStore::new();
    // str.to_re("") matches the empty string at every position.
    // Leftmost shortest → position 0, length 0.
    let r = mk_str_to_re(&mut terms, "");
    match RegExpSolver::find_first_match(&terms, "abc", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 0);
        }
        other => panic!("expected Found(0,0), got {other:?}"),
    }
}

#[test]
fn find_first_match_re_none_no_match() {
    let mut terms = TermStore::new();
    let r = mk_re_none(&mut terms);
    assert!(matches!(
        RegExpSolver::find_first_match(&terms, "abc", r),
        MatchResult::NoMatch
    ));
}

#[test]
fn find_first_match_union_picks_shortest() {
    let mut terms = TermStore::new();
    // re.union(str.to_re("a"), str.to_re("ab"))
    // In "xab", leftmost match starts at 1. Shortest at that position is "a".
    let a = mk_str_to_re(&mut terms, "a");
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_union(&mut terms, vec![a, ab]);
    match RegExpSolver::find_first_match(&terms, "xab", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 1);
            assert_eq!(end, 2); // "a" (1 byte)
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_re_star_matches_empty() {
    let mut terms = TermStore::new();
    // re.*(str.to_re("a")) matches "" at position 0 (shortest).
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_star(&mut terms, a);
    match RegExpSolver::find_first_match(&terms, "bbb", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 0);
        }
        other => panic!("expected Found(0,0), got {other:?}"),
    }
}

#[test]
fn find_first_match_range_digit() {
    let mut terms = TermStore::new();
    let r = mk_re_range(&mut terms, "0", "9");
    match RegExpSolver::find_first_match(&terms, "abc5def", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 3);
            assert_eq!(end, 4);
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_empty_string_empty_regex() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "");
    match RegExpSolver::find_first_match(&terms, "", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 0);
        }
        other => panic!("expected Found(0,0), got {other:?}"),
    }
}

#[test]
fn find_first_match_empty_string_nonempty_regex() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "a");
    assert!(matches!(
        RegExpSolver::find_first_match(&terms, "", r),
        MatchResult::NoMatch
    ));
}

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId};

use super::super::super::Executor;
use super::super::skolem_cache::ExecutorSkolemCache;
use super::OverlapMergeResult;

#[test]
fn extract_strlen_eq_const_accepts_string_length_equalities() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let three = exec.ctx.terms.mk_int(BigInt::from(3));

    assert_eq!(exec.extract_strlen_eq_const(len_x, three), Some((x, 3)));
}

#[test]
fn extract_strlen_eq_const_rejects_non_length_terms() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let three = exec.ctx.terms.mk_int(BigInt::from(3));

    assert_eq!(exec.extract_strlen_eq_const(x, three), None);
    assert_eq!(exec.extract_strlen_eq_const(y, x), None);
}

#[test]
fn concat_edge_constants_reads_prefix_only() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![ab, x], Sort::String);

    assert_eq!(
        exec.concat_edge_constants(concat),
        Some((Some("ab".to_string()), None))
    );
}

#[test]
fn concat_edge_constants_reads_suffix_only() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let bc = exec.ctx.terms.mk_string("bc".to_string());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![x, bc], Sort::String);

    assert_eq!(
        exec.concat_edge_constants(concat),
        Some((None, Some("bc".to_string())))
    );
}

#[test]
fn concat_edge_constants_reads_both_edges() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let cd = exec.ctx.terms.mk_string("cd".to_string());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![ab, x, cd], Sort::String);

    assert_eq!(
        exec.concat_edge_constants(concat),
        Some((Some("ab".to_string()), Some("cd".to_string())))
    );
}

#[test]
fn concat_edge_constants_rejects_terms_without_constant_edges() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);

    assert_eq!(exec.concat_edge_constants(concat), None);
}

#[test]
fn merge_prefix_suffix_exact_len_infers_unique_string() {
    match Executor::merge_prefix_suffix_exact_len("ab", "bc", 3) {
        OverlapMergeResult::Merged(s) => assert_eq!(s, "abc"),
        other => panic!("expected Merged(\"abc\"), got {other:?}"),
    }
}

#[test]
fn merge_prefix_suffix_exact_len_rejects_incompatible_overlap() {
    assert!(
        matches!(
            Executor::merge_prefix_suffix_exact_len("ab", "cd", 3),
            OverlapMergeResult::Conflict
        ),
        "incompatible overlap must return Conflict"
    );
}

#[test]
fn preregister_overlap_constant_equalities_emits_expected_equality() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let bc = exec.ctx.terms.mk_string("bc".to_string());
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_eq = exec.ctx.terms.mk_eq(len_x, three);
    let prefix = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.prefixof"), vec![ab, x], Sort::Bool);
    let suffix = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.suffixof"), vec![bc, x], Sort::Bool);

    let inferred = exec.preregister_overlap_constant_equalities(&[prefix, suffix, len_eq]);
    let abc = exec.ctx.terms.mk_string("abc".to_string());
    let expected = exec.ctx.terms.mk_eq(x, abc);

    assert!(
        inferred.contains(&expected),
        "prefix/suffix overlap with fixed length must infer x = \"abc\""
    );
}

#[test]
fn preregister_overlap_constant_equalities_reads_concat_equations() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let sk1 = exec.ctx.terms.mk_fresh_var("sk1", Sort::String);
    let sk2 = exec.ctx.terms.mk_fresh_var("sk2", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let bc = exec.ctx.terms.mk_string("bc".to_string());
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let left_concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![ab, sk1], Sort::String);
    let right_concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![sk2, bc], Sort::String);
    let eq1 = exec.ctx.terms.mk_eq(x, left_concat);
    let eq2 = exec.ctx.terms.mk_eq(x, right_concat);
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_eq = exec.ctx.terms.mk_eq(len_x, three);

    let inferred = exec.preregister_overlap_constant_equalities(&[eq1, eq2, len_eq]);
    let abc = exec.ctx.terms.mk_string("abc".to_string());
    let expected = exec.ctx.terms.mk_eq(x, abc);

    assert!(
        inferred.contains(&expected),
        "concat overlap with fixed length must infer x = \"abc\""
    );
}

#[test]
fn merge_prefix_suffix_exact_len_undetermined_for_free_middle() {
    // Target length exceeds prefix + suffix: free middle chars → undetermined.
    assert!(
        matches!(
            Executor::merge_prefix_suffix_exact_len("ab", "cd", 10),
            OverlapMergeResult::Undetermined
        ),
        "free middle characters must return Undetermined"
    );
}

#[test]
fn merge_prefix_suffix_exact_len_conflict_for_too_short_target() {
    // Target length shorter than either prefix or suffix alone.
    assert!(
        matches!(
            Executor::merge_prefix_suffix_exact_len("abc", "def", 2),
            OverlapMergeResult::Conflict
        ),
        "target too short for prefix or suffix must return Conflict"
    );
}

#[test]
fn collect_str_at_variables_finds_str_at_first_arg() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let at_term = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.at"), vec![x, zero], Sort::String);
    // Wrap in an equality to simulate an assertion tree.
    let hello = exec.ctx.terms.mk_string("a".to_string());
    let eq = exec.ctx.terms.mk_eq(at_term, hello);

    let vars = exec.collect_str_at_variables(&[eq]);

    assert!(vars.contains(&x), "x must be collected as str.at variable");
    assert!(!vars.contains(&y), "y must not appear without str.at");
}

#[test]
fn collect_str_at_variables_recurses_through_negation_and_ite() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let at_term = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.at"), vec![x, zero], Sort::String);
    let a = exec.ctx.terms.mk_string("a".to_string());
    let eq = exec.ctx.terms.mk_eq(at_term, a);
    let neg = exec.ctx.terms.mk_not(eq);
    let cond = exec.ctx.terms.mk_fresh_var("c", Sort::Bool);
    let tt = exec.ctx.terms.true_term();
    let ite = exec.ctx.terms.mk_ite(cond, neg, tt);

    let vars = exec.collect_str_at_variables(&[ite]);

    assert!(
        vars.contains(&x),
        "str.at variable must be found through Not + ITE nesting"
    );
}

#[test]
fn preregister_contains_decompositions_emits_implication_for_positive_contains() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let mut contains_decomposed = hashbrown::HashSet::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let contains = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.contains"), vec![x, y], Sort::Bool);

    let decomps = exec.preregister_contains_decompositions(
        &[contains],
        &mut cache,
        &mut decomposed,
        &mut contains_decomposed,
    );

    // Must produce at least the implication and non-negativity axioms.
    assert!(
        decomps.len() >= 3,
        "contains decomposition must produce implication + 2 non-neg + length norm, got {}",
        decomps.len()
    );

    // First decomposition should be an implication: contains(x,y) => x = sk_pre ++ y ++ sk_post
    // mk_implies desugars to or(not(a), b), but mk_or sorts args by TermId,
    // so the negation may appear at either position.
    let first = decomps[0];
    match exec.ctx.terms.get(first) {
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
            // Find which arg is the negation and which is the consequent.
            let (ante, cons) = if matches!(exec.ctx.terms.get(args[0]), TermData::Not(_)) {
                (args[0], args[1])
            } else if matches!(exec.ctx.terms.get(args[1]), TermData::Not(_)) {
                (args[1], args[0])
            } else {
                panic!("implication must have a negated antecedent in either position")
            };
            // Antecedent should be ¬contains(x, y)
            match exec.ctx.terms.get(ante) {
                TermData::Not(inner) => {
                    assert_eq!(*inner, contains, "antecedent must negate contains")
                }
                _ => unreachable!(),
            }
            // Consequent should be an equality x = str.++(...)
            match exec.ctx.terms.get(cons) {
                TermData::App(Symbol::Named(name), args) if name == "=" => {
                    assert_eq!(args[0], x, "equality lhs must be x");
                    match exec.ctx.terms.get(args[1]) {
                        TermData::App(Symbol::Named(cname), cargs) if cname == "str.++" => {
                            assert_eq!(cargs.len(), 3, "concat must have 3 args: pre, y, post");
                            assert_eq!(cargs[1], y, "middle concat arg must be y");
                        }
                        _ => panic!("rhs must be str.++ concat"),
                    }
                }
                _ => panic!("consequent must be an equality"),
            }
        }
        _ => panic!(
            "first decomposition must be an implication (or(not(.),.)): {:?}",
            exec.ctx.terms.get(first)
        ),
    }
}

#[test]
fn preregister_contains_decompositions_skips_reflexive_contains() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let mut contains_decomposed = hashbrown::HashSet::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    // str.contains(x, x) — reflexive, should be skipped.
    let contains = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.contains"), vec![x, x], Sort::Bool);

    let decomps = exec.preregister_contains_decompositions(
        &[contains],
        &mut cache,
        &mut decomposed,
        &mut contains_decomposed,
    );

    assert!(
        decomps.is_empty(),
        "reflexive contains(x, x) must produce zero decompositions"
    );
}

#[test]
fn preregister_contains_decompositions_emits_decomposition_for_prefixof() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let mut contains_decomposed = hashbrown::HashSet::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let prefixof = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.prefixof"), vec![ab, x], Sort::Bool);

    let decomps = exec.preregister_contains_decompositions(
        &[prefixof],
        &mut cache,
        &mut decomposed,
        &mut contains_decomposed,
    );

    let consequence = decomps
        .iter()
        .find_map(|&term| {
            let (antecedent, consequent) = implication_parts(&exec.ctx.terms, term)?;
            (antecedent == prefixof).then_some(consequent)
        })
        .expect("prefixof preregistration must emit a guarded consequence");
    let concat = equality_other_side_for_subject(&exec.ctx.terms, consequence, x)
        .expect("prefixof consequence must constrain x");

    match exec.ctx.terms.get(concat) {
        TermData::App(Symbol::Named(name), args) if name == "str.++" => {
            assert_eq!(args.len(), 2, "prefixof concat must have 2 args");
            assert_eq!(args[0], ab, "prefixof concat must start with the prefix");
        }
        _ => panic!("prefixof consequence must build a concat"),
    }
}

#[test]
fn preregister_contains_decompositions_emits_decomposition_for_suffixof() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let mut contains_decomposed = hashbrown::HashSet::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let cd = exec.ctx.terms.mk_string("cd".to_string());
    let suffixof = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.suffixof"), vec![cd, x], Sort::Bool);

    let decomps = exec.preregister_contains_decompositions(
        &[suffixof],
        &mut cache,
        &mut decomposed,
        &mut contains_decomposed,
    );

    let consequence = decomps
        .iter()
        .find_map(|&term| {
            let (antecedent, consequent) = implication_parts(&exec.ctx.terms, term)?;
            (antecedent == suffixof).then_some(consequent)
        })
        .expect("suffixof preregistration must emit a guarded consequence");
    let concat = equality_other_side_for_subject(&exec.ctx.terms, consequence, x)
        .expect("suffixof consequence must constrain x");

    match exec.ctx.terms.get(concat) {
        TermData::App(Symbol::Named(name), args) if name == "str.++" => {
            assert_eq!(args.len(), 2, "suffixof concat must have 2 args");
            assert_eq!(args[1], cd, "suffixof concat must end with the suffix");
        }
        _ => panic!("suffixof consequence must build a concat"),
    }
}

#[test]
fn preregister_contains_blocks_contains_after_prefix_decomposition() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let mut contains_decomposed = hashbrown::HashSet::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    // The preregister walk is LIFO over the assertion slice, so pass
    // contains first and prefix second to ensure prefixof claims x before
    // the contains atom is considered.
    let prefixof = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.prefixof"), vec![ab, x], Sort::Bool);
    let contains = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.contains"), vec![x, y], Sort::Bool);

    let decomps = exec.preregister_contains_decompositions(
        &[contains, prefixof],
        &mut cache,
        &mut decomposed,
        &mut contains_decomposed,
    );

    assert_has_guarded_antecedent(
        &exec.ctx.terms,
        &decomps,
        prefixof,
        "prefix decomposition must still be emitted",
    );
    assert_lacks_guarded_antecedent(
        &exec.ctx.terms,
        &decomps,
        contains,
        "contains implication must be absent once prefix claimed the variable",
    );

    // The contains decomposition should be skipped because prefix already
    // claimed the variable (bidirectional guard).
    assert!(
        !contains_decomposed.contains(&x),
        "contains must not decompose a variable already claimed by prefix"
    );
}

#[test]
fn preregister_extf_reductions_emits_substr_reduction_with_constant_bounds() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let s = exec.ctx.terms.mk_fresh_var("s", Sort::String);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let two = exec.ctx.terms.mk_int(BigInt::from(2));
    let substr =
        exec.ctx
            .terms
            .mk_app(Symbol::named("str.substr"), vec![s, one, two], Sort::String);
    // Put substr in an equality assertion so it gets discovered.
    let result = exec.ctx.terms.mk_fresh_var("r", Sort::String);
    let eq = exec.ctx.terms.mk_eq(result, substr);

    let (reductions, reduced_ids) = exec.preregister_extf_reductions(
        &[eq],
        &mut cache,
        &mut decomposed,
        true,  // enable_substr_and_at
        false, // disable replace
    );

    // Must produce: ITE reduction + bridge equality + non-neg/bridge per skolem.
    assert!(
        reductions.len() >= 2,
        "substr reduction must produce at least ITE + bridge, got {}",
        reductions.len()
    );
    assert!(
        reduced_ids.contains(&substr),
        "substr term must be in reduced_term_ids"
    );

    let skt = assert_top_level_bridge(
        &exec.ctx.terms,
        &reductions,
        substr,
        "substr preregistration must bridge substr term to a result skolem",
    );
    assert_roots_have_concat_equality(
        &exec.ctx.terms,
        &reductions,
        s,
        3,
        &[(1, skt)],
        "substr preregistration must constrain s = str.++(sk_pre, skt, sk_suf)",
    );
    let len_skt = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
    let len_bound = exec.ctx.terms.mk_le(len_skt, two);
    assert_roots_contain_term(
        &exec.ctx.terms,
        &reductions,
        len_bound,
        "substr preregistration must preserve len(skt) <= m",
    );
}

#[test]
fn preregister_extf_reductions_skips_ground_substr() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let hello = exec.ctx.terms.mk_string("hello".to_string());
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    // Fully ground: str.substr("hello", 1, 3) evaluates to "ell".
    let substr = exec.ctx.terms.mk_app(
        Symbol::named("str.substr"),
        vec![hello, one, three],
        Sort::String,
    );
    let r = exec.ctx.terms.mk_fresh_var("r", Sort::String);
    let eq = exec.ctx.terms.mk_eq(r, substr);

    let (reductions, reduced_ids) =
        exec.preregister_extf_reductions(&[eq], &mut cache, &mut decomposed, true, false);

    assert!(
        reductions.is_empty(),
        "ground substr must be skipped (handled by fold_ground_string_ops)"
    );
    assert!(
        !reduced_ids.contains(&substr),
        "ground substr must not appear in reduced_term_ids"
    );
}

#[test]
fn preregister_extf_reductions_emits_replace_reduction() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let z = exec.ctx.terms.mk_fresh_var("z", Sort::String);
    let replace = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.replace"), vec![x, y, z], Sort::String);
    let r = exec.ctx.terms.mk_fresh_var("r", Sort::String);
    let eq = exec.ctx.terms.mk_eq(r, replace);

    let (reductions, reduced_ids) = exec.preregister_extf_reductions(
        &[eq],
        &mut cache,
        &mut decomposed,
        false, // disable substr
        true,  // enable replace
    );

    // Must produce: ITE + bridge + non-neg/bridge per skolem.
    assert!(
        reductions.len() >= 2,
        "replace reduction must produce at least ITE + bridge, got {}",
        reductions.len()
    );
    assert!(
        reduced_ids.contains(&replace),
        "replace term must be in reduced_term_ids"
    );

    let rpw = assert_top_level_bridge(
        &exec.ctx.terms,
        &reductions,
        replace,
        "replace preregistration must bridge replace term to its result skolem",
    );
    assert_roots_have_concat_equality(
        &exec.ctx.terms,
        &reductions,
        x,
        3,
        &[(1, y)],
        "replace preregistration must decompose x around the needle",
    );
    assert_roots_have_concat_equality(
        &exec.ctx.terms,
        &reductions,
        rpw,
        3,
        &[(1, z)],
        "replace preregistration must rebuild the result around the replacement",
    );
}

#[test]
fn preregister_extf_reductions_emits_str_at_reduction() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let s = exec.ctx.terms.mk_fresh_var("s", Sort::String);
    let n = exec.ctx.terms.mk_fresh_var("n", Sort::Int);
    let at = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.at"), vec![s, n], Sort::String);
    let r = exec.ctx.terms.mk_fresh_var("r", Sort::String);
    let eq = exec.ctx.terms.mk_eq(r, at);

    let (reductions, reduced_ids) = exec.preregister_extf_reductions(
        &[eq],
        &mut cache,
        &mut decomposed,
        true,  // enable_substr_and_at
        false, // disable replace
    );

    assert!(
        reductions.len() >= 2,
        "str.at reduction must produce at least implication + bridge, got {}",
        reductions.len()
    );
    assert!(
        reduced_ids.contains(&at),
        "str.at term must be in reduced_term_ids"
    );

    let skt = assert_top_level_bridge(
        &exec.ctx.terms,
        &reductions,
        at,
        "str.at preregistration must bridge str.at term to a result skolem",
    );
    assert_roots_have_concat_equality(
        &exec.ctx.terms,
        &reductions,
        s,
        3,
        &[(1, skt)],
        "str.at preregistration must constrain s = str.++(sk1, skt, sk2)",
    );
    let len_skt = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![skt], Sort::Int);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let unit_len = exec.ctx.terms.mk_eq(len_skt, one);
    assert_roots_contain_term(
        &exec.ctx.terms,
        &reductions,
        unit_len,
        "str.at preregistration must constrain the result skolem to unit length",
    );
}

#[test]
fn preregister_contains_emits_pairwise_combined_length_bounds() {
    let mut exec = Executor::new();
    let mut cache = ExecutorSkolemCache::new();
    let mut decomposed = hashbrown::HashSet::new();
    let mut contains_decomposed = hashbrown::HashSet::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let cd = exec.ctx.terms.mk_string("cd".to_string());
    let c1 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.contains"), vec![x, ab], Sort::Bool);
    let c2 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.contains"), vec![x, cd], Sort::Bool);

    let decomps = exec.preregister_contains_decompositions(
        &[c1, c2],
        &mut cache,
        &mut decomposed,
        &mut contains_decomposed,
    );

    // With "ab" and "cd" (no overlap), combined min len = 4.
    // Each individual len >= 2. Combined 4 > max individual 2 → bound emitted.
    // Check that at least one decomposition contains a len(x) >= 4 bound.
    let len_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let four = exec.ctx.terms.mk_int(BigInt::from(4));
    let ge_4 = exec.ctx.terms.mk_ge(len_x, four);

    let has_combined_bound = decomps.iter().any(|&d| {
        // The bound is guarded by (and c1 c2) => ge_4, check for ge_4 in the term tree.
        term_contains(&exec.ctx.terms, d, ge_4)
    });

    assert!(
        has_combined_bound,
        "pairwise combined length bound len(x) >= 4 must be emitted for non-overlapping patterns"
    );
}

fn implication_parts(terms: &z4_core::TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 2 => {
            if let TermData::Not(inner) = terms.get(args[0]) {
                Some((*inner, args[1]))
            } else if let TermData::Not(inner) = terms.get(args[1]) {
                Some((*inner, args[0]))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn assert_has_guarded_antecedent(
    terms: &z4_core::TermStore,
    roots: &[TermId],
    antecedent: TermId,
    message: &str,
) {
    assert!(
        roots.iter().any(|&term| {
            matches!(
                implication_parts(terms, term),
                Some((candidate, _)) if candidate == antecedent
            )
        }),
        "{message}"
    );
}

fn assert_lacks_guarded_antecedent(
    terms: &z4_core::TermStore,
    roots: &[TermId],
    antecedent: TermId,
    message: &str,
) {
    assert!(
        roots.iter().all(|&term| {
            !matches!(
                implication_parts(terms, term),
                Some((candidate, _)) if candidate == antecedent
            )
        }),
        "{message}"
    );
}

fn equality_other_side_for_subject(
    terms: &z4_core::TermStore,
    term: TermId,
    subject: TermId,
) -> Option<TermId> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            if args[0] == subject {
                Some(args[1])
            } else if args[1] == subject {
                Some(args[0])
            } else {
                None
            }
        }
        _ => None,
    }
}

fn find_top_level_equality_other_side(
    terms: &z4_core::TermStore,
    roots: &[TermId],
    subject: TermId,
) -> Option<TermId> {
    roots
        .iter()
        .find_map(|&term| equality_other_side_for_subject(terms, term, subject))
}

fn assert_top_level_bridge(
    terms: &z4_core::TermStore,
    roots: &[TermId],
    subject: TermId,
    message: &str,
) -> TermId {
    find_top_level_equality_other_side(terms, roots, subject).unwrap_or_else(|| panic!("{message}"))
}

fn assert_roots_have_concat_equality(
    terms: &z4_core::TermStore,
    roots: &[TermId],
    subject: TermId,
    concat_arity: usize,
    known_args: &[(usize, TermId)],
    message: &str,
) {
    assert!(
        roots.iter().any(|&term| {
            term_contains_concat_equality(terms, term, subject, concat_arity, known_args)
        }),
        "{message}"
    );
}

fn assert_roots_contain_term(
    terms: &z4_core::TermStore,
    roots: &[TermId],
    needle: TermId,
    message: &str,
) {
    assert!(
        roots.iter().any(|&term| term_contains(terms, term, needle)),
        "{message}"
    );
}

fn term_contains_concat_equality(
    terms: &z4_core::TermStore,
    root: TermId,
    subject: TermId,
    concat_arity: usize,
    known_args: &[(usize, TermId)],
) -> bool {
    if let Some(other_side) = equality_other_side_for_subject(terms, root, subject) {
        if let TermData::App(Symbol::Named(name), args) = terms.get(other_side) {
            if name == "str.++"
                && args.len() == concat_arity
                && known_args
                    .iter()
                    .all(|(index, expected)| args[*index] == *expected)
            {
                return true;
            }
        }
    }

    match terms.get(root) {
        TermData::App(_, args) => args.iter().any(|&arg| {
            term_contains_concat_equality(terms, arg, subject, concat_arity, known_args)
        }),
        TermData::Not(inner) => {
            term_contains_concat_equality(terms, *inner, subject, concat_arity, known_args)
        }
        TermData::Ite(c, t, e) => {
            term_contains_concat_equality(terms, *c, subject, concat_arity, known_args)
                || term_contains_concat_equality(terms, *t, subject, concat_arity, known_args)
                || term_contains_concat_equality(terms, *e, subject, concat_arity, known_args)
        }
        _ => false,
    }
}

/// Helper: check if `needle` appears anywhere in the term DAG rooted at `root`.
fn term_contains(terms: &z4_core::TermStore, root: TermId, needle: TermId) -> bool {
    if root == needle {
        return true;
    }
    match terms.get(root) {
        TermData::App(_, args) => args.iter().any(|&a| term_contains(terms, a, needle)),
        TermData::Not(inner) => term_contains(terms, *inner, needle),
        TermData::Ite(c, t, e) => {
            term_contains(terms, *c, needle)
                || term_contains(terms, *t, needle)
                || term_contains(terms, *e, needle)
        }
        _ => false,
    }
}

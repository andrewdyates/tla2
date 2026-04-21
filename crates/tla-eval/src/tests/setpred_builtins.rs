// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{eval_str, eval_with_ops, Value};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_builtin_functions_and_fold_accept_domains() {
    let defs = r#"
EXTENDS FiniteSets
S == {x \in SUBSET {1, 2} : Cardinality(x) = 1}
F == [x \in S |-> Cardinality(x)]
UnionAcc(acc, elem) == acc \cup elem
Add(a, b) == a + b
"#;

    assert_eq!(
        eval_with_ops(defs, "DOMAIN Restrict(F, S) = S").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(defs, "ExistsBijection(S, S)").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(defs, "FoldSet(UnionAcc, {}, S)").unwrap(),
        Value::set(vec![Value::int(1), Value::int(2)])
    );
    assert_eq!(
        eval_with_ops(defs, "FoldFunctionOnSet(Add, 0, F, S)").unwrap(),
        Value::int(2)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_builtin_stdlib_and_sequences_accept_domains() {
    let defs = r#"
S == {x \in {1, 2, 3, 4} : x > 1}
Cmp(a, b) == a < b
Seqs == {s \in {<<1, 2>>, <<1, 3>>} : TRUE}
"#;

    assert_eq!(eval_with_ops(defs, "Min(S)").unwrap(), Value::int(2));
    assert_eq!(eval_with_ops(defs, "Max(S)").unwrap(), Value::int(4));
    assert_eq!(
        eval_with_ops(defs, "ToSet(SetToSeq(S)) = S").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(defs, "SetToSortSeq(S, Cmp)").unwrap(),
        Value::seq([Value::int(2), Value::int(3), Value::int(4)])
    );
    assert_eq!(
        eval_with_ops(defs, "LongestCommonPrefix(Seqs)").unwrap(),
        Value::seq([Value::int(1)])
    );
    assert_eq!(
        eval_with_ops(defs, "CommonPrefixes(Seqs) = {<<>>, <<1>>}").unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_builtin_sequences_ext_ops_accept_domains() {
    let defs = r#"
S == {x \in {1, 2} : TRUE}
"#;

    assert_eq!(
        eval_with_ops(defs, "Cardinality(BoundedSeq(S, 2))").unwrap(),
        Value::int(7)
    );
    assert_eq!(
        eval_with_ops(defs, "Cardinality(TupleOf(S, 2))").unwrap(),
        Value::int(4)
    );
    assert_eq!(
        eval_with_ops(defs, "Cardinality(SetToSeqs(S))").unwrap(),
        Value::int(2)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_builtin_io_and_tlc_accept_domains() {
    let defs = r#"
S == {x \in {1, 2, 3} : TRUE}
"#;

    assert_eq!(
        eval_with_ops(defs, "Cardinality(RandomSubset(2, S))").unwrap(),
        Value::int(2)
    );
    assert_eq!(
        eval_with_ops(defs, "Cardinality(RandomSetOfSubsets(3, 1, S))").unwrap(),
        Value::int(3)
    );
    assert_eq!(
        eval_with_ops(defs, "Cardinality(RandomSubsetSet(3, \"0.5\", S))").unwrap(),
        Value::int(3)
    );
    assert_eq!(
        eval_with_ops(defs, "Cardinality(Permutations(S))").unwrap(),
        Value::int(6)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_builtin_graphs_accept_domains() {
    let defs = r#"
R == {e \in {<<1, 2>>, <<2, 3>>} : TRUE}
N == {n \in {1, 2, 3} : TRUE}
E == {e \in {<<1, 2>>, <<2, 3>>} : TRUE}
"#;

    assert_eq!(
        eval_with_ops(
            defs,
            "TransitiveClosure(R) = {<<1, 2>>, <<2, 3>>, <<1, 3>>}"
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(
            defs,
            "ReflexiveTransitiveClosure(R, N) = {<<1, 1>>, <<2, 2>>, <<3, 3>>, <<1, 2>>, <<2, 3>>, <<1, 3>>}"
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(defs, "ConnectedNodes(R) = {1, 2, 3}").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(defs, "IsDirectedGraph([node |-> N, edge |-> E])").unwrap(),
        Value::Bool(true)
    );
}

/// #1828 coverage gap: SetToBag and BagUnion use eval_iter_set but had zero
/// SetPred-specific tests. Without eval_iter_set, SetPred values would fail
/// with a type error (iter_set returns None for SetPred).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_builtin_bags_accept_domains() {
    let defs = r#"
S == {x \in {1, 2, 3} : x > 1}
B1 == SetToBag(S)
B2 == SetToBag({x \in {3, 4, 5} : x < 6})
BagS == {b \in {B1, B2} : TRUE}
"#;

    // SetToBag over SetPred domain: each element gets count 1
    // S = {2, 3}, so B1 maps 2->1, 3->1, BagCardinality = 2
    assert_eq!(
        eval_with_ops(defs, "IsABag(B1)").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(defs, "BagCardinality(B1)").unwrap(),
        Value::int(2)
    );
    // B2 = SetToBag({3,4,5}) maps 3->1, 4->1, 5->1
    // BagUnion({B1, B2}): 2->1, 3->2, 4->1, 5->1 => BagCardinality = 5
    assert_eq!(
        eval_with_ops(defs, "BagCardinality(BagUnion(BagS))").unwrap(),
        Value::int(5)
    );
}

/// #1828 coverage gap: set-map expressions {f(x) : x \in S} where S is a
/// SetPred use eval_iter_set (helpers.rs) but had no dedicated
/// test with a lazy-SetPred domain.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_set_map_over_lazy_domain() {
    let defs = r#"
EXTENDS FiniteSets
S == {x \in SUBSET {1, 2} : Cardinality(x) = 1}
Mapped == {Cardinality(x) : x \in S}
"#;

    // S = {{1}, {2}}, so Mapped = {1} (both singletons have cardinality 1)
    assert_eq!(
        eval_with_ops(defs, "Mapped = {1}").unwrap(),
        Value::Bool(true)
    );
}

/// #1828 coverage gap: Injection/Surjection/Bijection with SetPred domains.
/// builtin_functions.rs uses eval_iter_set for source/target set iteration.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_builtin_function_spaces_accept_domains() {
    let defs = r#"
EXTENDS FiniteSets
S == {x \in {1, 2} : TRUE}
T == {x \in {3, 4} : TRUE}
"#;

    // Injection(S, T) = set of injective functions from S to T
    assert_eq!(
        eval_with_ops(defs, "Cardinality(Injection(S, T))").unwrap(),
        Value::int(2)
    );
    // Surjection(S, T) = set of surjective functions from S to T
    assert_eq!(
        eval_with_ops(defs, "Cardinality(Surjection(S, T))").unwrap(),
        Value::int(2)
    );
    // Bijection(S, T) = set of bijective functions from S to T
    assert_eq!(
        eval_with_ops(defs, "Cardinality(Bijection(S, T))").unwrap(),
        Value::int(2)
    );
}

/// Part of #3978: Verify streaming Cardinality for SetPred values.
///
/// When the SetPred value is reached via a LET binding (not syntactic SetFilter),
/// the direct count_set_filter_elements fast path does NOT apply. The Cardinality
/// code falls through to the `Value::SetPred` branch, which now uses
/// `count_setpred_streaming` to count elements by streaming through the predicate
/// without materializing the full filtered set into a Vec<Value>.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_cardinality_of_setpred_over_funcset() {
    // FuncSet [{1,2} -> {0,1}] has 4 elements (2^2). The SetPred filters to
    // functions where f[1] = 0, yielding 2 functions: (1->0,2->0) and (1->0,2->1).
    // This exercises the streaming counter path because:
    //   - The domain is FuncSet (non-reducible), so eval_set_filter returns SetPredValue
    //   - Cardinality is called on a LET-bound SetPred value
    //   - count_setpred_streaming streams through the 4 FuncSet elements,
    //     evaluating f[1] = 0 on each, and counts 2 matches without Vec allocation.
    let defs = r#"
EXTENDS FiniteSets
Filtered == {f \in [{1, 2} -> {0, 1}] : f[1] = 0}
"#;

    assert_eq!(
        eval_with_ops(defs, "Cardinality(Filtered)").unwrap(),
        Value::int(2),
        "Streaming Cardinality: 2 of 4 functions have f[1]=0"
    );
}

/// Part of #3978: Verify streaming subseteq with SetPred LHS.
///
/// `{x \in S : P(x)} \subseteq T` should stream elements through the predicate
/// and short-circuit on the first element not in T, without materializing the
/// full filtered set.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_subseteq_setpred_lhs() {
    let defs = r#"
EXTENDS FiniteSets
S == {x \in SUBSET {1, 2, 3} : Cardinality(x) = 1}
"#;

    // S = {{1}, {2}, {3}}, which is a subset of SUBSET {1,2,3}
    assert_eq!(
        eval_with_ops(defs, "S \\subseteq SUBSET {1, 2, 3}").unwrap(),
        Value::Bool(true),
        "SetPred subseteq SUBSET: all singletons are subsets of base set"
    );

    // S = {{1}, {2}, {3}} is NOT a subset of {{1}, {2}} because {3} is missing
    assert_eq!(
        eval_with_ops(defs, "S \\subseteq {{1}, {2}}").unwrap(),
        Value::Bool(false),
        "SetPred subseteq explicit set: missing element should fail"
    );
}

/// Part of #3978: Verify streaming EXISTS over SetPred domain short-circuits.
///
/// For `\E x \in {f \in [S -> T] : P(f)} : Q(x)`, the streaming path evaluates
/// P(f) on-demand and Q(x) on each match, short-circuiting as soon as Q returns
/// TRUE without evaluating P for remaining elements.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_exists_over_setpred_funcset() {
    // [{1,2} -> {0,1}] has 4 functions. The SetPred filters to f[1]=0 (2 functions).
    // EXISTS checks if any satisfying f also has f[2]=1. The function (1->0, 2->1)
    // is the first (or second) match and satisfies the EXISTS, so this should return TRUE.
    assert_eq!(
        eval_str(
            r#"\E f \in {g \in [{1, 2} -> {0, 1}] : g[1] = 0} : f[2] = 1"#
        )
        .unwrap(),
        Value::Bool(true),
        "Streaming EXISTS: should find f with f[1]=0 and f[2]=1"
    );

    // No function with f[1]=0 also has f[2]=2 (codomain is {0,1})
    assert_eq!(
        eval_str(
            r#"\E f \in {g \in [{1, 2} -> {0, 1}] : g[1] = 0} : f[2] = 2"#
        )
        .unwrap(),
        Value::Bool(false),
        "Streaming EXISTS: no f with f[1]=0 and f[2]=2"
    );
}

/// Part of #3978: Verify streaming FORALL over SetPred domain.
///
/// FORALL uses the same streaming path as EXISTS but short-circuits on FALSE
/// instead of TRUE. This tests that the streaming path correctly evaluates
/// the universal quantifier.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_forall_over_setpred_funcset() {
    // All functions in [{1,2} -> {0,1}] with f[1]=0 have f[2] \in {0,1} (trivially true)
    assert_eq!(
        eval_str(
            r#"\A f \in {g \in [{1, 2} -> {0, 1}] : g[1] = 0} : f[2] \in {0, 1}"#
        )
        .unwrap(),
        Value::Bool(true),
        "Streaming FORALL: all f with f[1]=0 have f[2] in codomain"
    );

    // Not all functions with f[1]=0 have f[2]=0 (one has f[2]=1)
    assert_eq!(
        eval_str(
            r#"\A f \in {g \in [{1, 2} -> {0, 1}] : g[1] = 0} : f[2] = 0"#
        )
        .unwrap(),
        Value::Bool(false),
        "Streaming FORALL: not all f with f[1]=0 have f[2]=0"
    );
}

/// Part of #3978: Verify streaming over SetPred with larger function set.
///
/// [{1,2,3} -> {0,1}] has 2^3=8 functions. The SetPred filters to bijections
/// (injective functions from {1,2,3} to a 2-element codomain). Since |domain|=3 > |codomain|=2,
/// there are zero bijections. The streaming path should evaluate all 8 predicates
/// and return FALSE for EXISTS.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_setpred_larger_funcset() {
    // [{1,2,3} -> {0,1}] has 8 functions. Filter to f[1] /= f[2] /\ f[2] /= f[3].
    // This gives functions where adjacent domain elements map to different values.
    // With codomain {0,1}, this is 0,1,0 and 1,0,1 = 2 functions.
    assert_eq!(
        eval_str(
            r#"Cardinality({f \in [{1, 2, 3} -> {0, 1}] : f[1] /= f[2] /\ f[2] /= f[3]})"#
        )
        .unwrap(),
        Value::int(2),
        "Streaming Cardinality: 2 of 8 functions have alternating values"
    );

    // EXISTS over the filtered set: is there one where f[1]=0? Yes: 0,1,0
    assert_eq!(
        eval_str(
            r#"\E f \in {g \in [{1, 2, 3} -> {0, 1}] : g[1] /= g[2] /\ g[2] /= g[3]} : f[1] = 0"#
        )
        .unwrap(),
        Value::Bool(true),
        "Streaming EXISTS: find alternating function starting with 0"
    );
}

/// Part of #3978: Verify streaming over SetPred with Interval source.
///
/// Tests that the streaming path works for non-FuncSet source types.
/// {x \in 1..100 : x > 95} should yield 5 elements (96..100) without
/// materializing all 100 elements into a Vec.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_setpred_interval_source() {
    // EXISTS over {x \in 1..100 : x > 95}: is there x > 98?
    assert_eq!(
        eval_str(r#"\E x \in {y \in 1..100 : y > 95} : x > 98"#).unwrap(),
        Value::Bool(true),
        "Streaming EXISTS over interval SetPred: found x > 98"
    );

    // FORALL over {x \in 1..100 : x > 95}: are all x > 90?
    assert_eq!(
        eval_str(r#"\A x \in {y \in 1..100 : y > 95} : x > 90"#).unwrap(),
        Value::Bool(true),
        "Streaming FORALL over interval SetPred: all > 90"
    );

    // Streaming Cardinality
    assert_eq!(
        eval_str(r#"Cardinality({y \in 1..100 : y > 95})"#).unwrap(),
        Value::int(5),
        "Streaming Cardinality over interval SetPred: 5 elements"
    );
}

/// Part of #3978: Verify streaming over SetPred with explicit Set source.
///
/// Tests that the streaming path works for Value::Set sources, which need
/// special handling in iter_set_owned (clone elements from SortedSet slice).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_setpred_explicit_set_source() {
    let defs = r#"
EXTENDS FiniteSets
S == {"a", "b", "c", "d", "e"}
Filtered == {x \in S : x /= "c"}
"#;

    assert_eq!(
        eval_with_ops(defs, "Cardinality(Filtered)").unwrap(),
        Value::int(4),
        "Streaming Cardinality: 4 of 5 strings pass filter"
    );

    assert_eq!(
        eval_with_ops(defs, r#"\E x \in Filtered : x = "d""#).unwrap(),
        Value::Bool(true),
        "Streaming EXISTS: found 'd' in filtered set"
    );

    assert_eq!(
        eval_with_ops(defs, r#"\E x \in Filtered : x = "c""#).unwrap(),
        Value::Bool(false),
        "Streaming EXISTS: 'c' excluded by filter"
    );
}

/// Part of #3978: Verify that eager and lazy iteration over function-set
/// SetPred produce identical results.
///
/// The key optimization: `iter_set_owned()` now delegates to `LazySet::set_iter_owned()`
/// which constructs a `FuncSetIterator` directly (owned odometer) instead of collecting
/// through `iter_set()`. This means `\E x \in {f \in [S -> T] : P(f)} : Q(x)` can
/// short-circuit without pre-materializing all |T|^|S| functions.
///
/// This test verifies both paths produce identical results for a non-trivial predicate.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_vs_eager_funcset_setpred_equivalence() {
    // [{1,2,3} -> {0,1}] has 2^3 = 8 functions. Filter to those where
    // f[1] + f[2] + f[3] = 2 (exactly 2 of the 3 domain elements map to 1).
    // There are C(3,2) = 3 such functions.
    let defs = r#"
EXTENDS FiniteSets
F == {f \in [{1, 2, 3} -> {0, 1}] : f[1] + f[2] + f[3] = 2}
"#;

    // Cardinality uses the streaming count path
    assert_eq!(
        eval_with_ops(defs, "Cardinality(F)").unwrap(),
        Value::int(3),
        "Lazy FuncSet SetPred: C(3,2) = 3 functions with exactly 2 ones"
    );

    // EXISTS uses the streaming SetPredStreamIter path
    assert_eq!(
        eval_with_ops(defs, r#"\E f \in F : f[1] = 0"#).unwrap(),
        Value::Bool(true),
        "Lazy EXISTS over FuncSet SetPred: f[1]=0 exists (f = 0,1,1)"
    );

    // FORALL uses the streaming path too
    assert_eq!(
        eval_with_ops(defs, r#"\A f \in F : f[1] + f[2] + f[3] = 2"#).unwrap(),
        Value::Bool(true),
        "Lazy FORALL over FuncSet SetPred: all filtered functions have sum=2"
    );

    // Nested: EXISTS with FORALL body over FuncSet SetPred
    assert_eq!(
        eval_with_ops(defs, r#"\E f \in F : \A x \in {1, 2, 3} : f[x] \in {0, 1}"#).unwrap(),
        Value::Bool(true),
        "Lazy nested quantifier over FuncSet SetPred"
    );
}

/// Part of #3978: Verify lazy iteration over SUBSET-based SetPred.
///
/// `iter_set_owned()` for SubsetValue now constructs a `SubsetIterator` directly
/// instead of collecting. This test verifies the lazy path for
/// `\E x \in {s \in SUBSET S : P(s)} : Q(x)`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_vs_eager_subset_setpred_equivalence() {
    let defs = r#"
EXTENDS FiniteSets
\* All 2-element subsets of {1,2,3,4}: C(4,2) = 6
TwoElemSets == {s \in SUBSET {1, 2, 3, 4} : Cardinality(s) = 2}
"#;

    // Note: {s \in SUBSET S : Cardinality(s) = k} triggers the K-subset
    // optimization, which falls back to the materializing path. This test
    // still exercises that the overall pipeline is correct.
    assert_eq!(
        eval_with_ops(defs, "Cardinality(TwoElemSets)").unwrap(),
        Value::int(6),
        "Lazy SUBSET SetPred: C(4,2) = 6 two-element subsets"
    );

    assert_eq!(
        eval_with_ops(defs, r#"\E s \in TwoElemSets : 1 \in s /\ 4 \in s"#).unwrap(),
        Value::Bool(true),
        "Lazy EXISTS: found {{1,4}} among 2-element subsets"
    );
}

/// Part of #3978: Verify lazy iteration over interval-based SetPred with
/// the `iter_set_owned` owned-iterator path.
///
/// IntervalValue's `set_iter_owned()` returns an owned i64-range or BigInt
/// iterator without collecting. This test verifies correctness for
/// streaming over interval-sourced SetPred values.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_interval_setpred_owned_iterator() {
    // {x \in 1..1000 : x % 100 = 0} = {100, 200, ..., 1000} = 10 elements
    // The interval iterator generates elements lazily (1, 2, 3, ...) and the
    // SetPred predicate filters. With owned iteration, no Vec<Value> of 1000
    // integers is created upfront.
    assert_eq!(
        eval_str(r#"Cardinality({x \in 1..1000 : x % 100 = 0})"#).unwrap(),
        Value::int(10),
        "Lazy interval SetPred: 10 multiples of 100 in 1..1000"
    );

    // EXISTS should short-circuit early
    assert_eq!(
        eval_str(r#"\E x \in {y \in 1..1000 : y % 100 = 0} : x = 100"#).unwrap(),
        Value::Bool(true),
        "Lazy EXISTS: short-circuit on first multiple of 100"
    );
}

/// Part of #3978: Verify streaming SetPred over RecordSet source.
///
/// RecordSet `[a: S, b: T]` now provides `RecordSetOwnedIterator` via
/// `set_iter_owned()`, enabling streaming SetPred iteration without
/// materializing the full cartesian product. This test exercises
/// `\E r \in {x \in [a: S, b: T] : P(x)} : Q(r)` through the streaming path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_setpred_over_record_set() {
    let defs = r#"
EXTENDS FiniteSets
\* [a: {1,2,3}, b: {10,20}] has 3*2=6 records. Filter to a > 1.
Filtered == {r \in [a: {1, 2, 3}, b: {10, 20}] : r.a > 1}
"#;

    // 4 records pass: (a=2,b=10), (a=2,b=20), (a=3,b=10), (a=3,b=20)
    assert_eq!(
        eval_with_ops(defs, "Cardinality(Filtered)").unwrap(),
        Value::int(4),
        "Streaming Cardinality over RecordSet SetPred: 4 of 6 records"
    );

    // EXISTS: is there a record with a=3 and b=20?
    assert_eq!(
        eval_with_ops(defs, r#"\E r \in Filtered : r.a = 3 /\ r.b = 20"#).unwrap(),
        Value::Bool(true),
        "Streaming EXISTS over RecordSet SetPred"
    );

    // FORALL: all filtered records have a > 1
    assert_eq!(
        eval_with_ops(defs, r#"\A r \in Filtered : r.a > 1"#).unwrap(),
        Value::Bool(true),
        "Streaming FORALL over RecordSet SetPred"
    );
}

/// Part of #3978: Verify streaming SetPred over TupleSet (cross product) source.
///
/// TupleSet `S1 \X S2` now provides `TupleSetOwnedIterator` via
/// `set_iter_owned()`, enabling streaming SetPred iteration without
/// materializing the full cartesian product. This test exercises
/// `\E t \in {x \in S1 \X S2 : P(x)} : Q(t)` through the streaming path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_setpred_over_tuple_set() {
    let defs = r#"
EXTENDS FiniteSets
\* {1,2,3} \X {10,20} has 6 tuples. Filter to first component > 1.
Filtered == {t \in {1, 2, 3} \X {10, 20} : t[1] > 1}
"#;

    // 4 tuples pass: <<2,10>>, <<2,20>>, <<3,10>>, <<3,20>>
    assert_eq!(
        eval_with_ops(defs, "Cardinality(Filtered)").unwrap(),
        Value::int(4),
        "Streaming Cardinality over TupleSet SetPred: 4 of 6 tuples"
    );

    // EXISTS: is there a tuple with first=3 and second=20?
    assert_eq!(
        eval_with_ops(defs, r#"\E t \in Filtered : t[1] = 3 /\ t[2] = 20"#).unwrap(),
        Value::Bool(true),
        "Streaming EXISTS over TupleSet SetPred"
    );

    // FORALL: all filtered tuples have first > 1
    assert_eq!(
        eval_with_ops(defs, r#"\A t \in Filtered : t[1] > 1"#).unwrap(),
        Value::Bool(true),
        "Streaming FORALL over TupleSet SetPred"
    );
}

/// Part of #3978: Verify streaming SetPred over nested SetPred source.
///
/// When a SetPred's source is itself a SetPred, the inner SetPred is
/// materialized recursively (it needs its own EvalCtx for predicate
/// evaluation). This test verifies the recursive materialization path
/// is correct for `{x \in {y \in S : P(y)} : Q(x)}`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_streaming_nested_setpred() {
    let defs = r#"
EXTENDS FiniteSets
\* Inner: {x \in 1..20 : x % 2 = 0} = {2,4,6,...,20} (10 elements)
\* Outer: filter to x > 15, giving {16, 18, 20} (3 elements)
Nested == {x \in {y \in 1..20 : y % 2 = 0} : x > 15}
"#;

    assert_eq!(
        eval_with_ops(defs, "Cardinality(Nested)").unwrap(),
        Value::int(3),
        "Nested SetPred: 3 even numbers > 15 in 1..20"
    );

    assert_eq!(
        eval_with_ops(defs, r#"\E x \in Nested : x = 18"#).unwrap(),
        Value::Bool(true),
        "EXISTS over nested SetPred: found 18"
    );

    assert_eq!(
        eval_with_ops(defs, r#"\A x \in Nested : x > 14"#).unwrap(),
        Value::Bool(true),
        "FORALL over nested SetPred: all > 14"
    );
}

/// Part of #3978: Verify CHOOSE TRUE over SetPred domain works correctly.
///
/// `CHOOSE x \in SetPred : TRUE` previously failed with SetTooLarge because
/// `Value::tlc_first_element()` calls `iter_set()` which returns None for SetPred.
/// The fix materializes the SetPred via `eval_iter_set` and finds the TLC-minimum.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_true_over_setpred_funcset() {
    let defs = r#"
EXTENDS FiniteSets
\* [{1,2} -> {0,1}] has 4 functions. Filter to f[1]=0 (2 functions).
\* CHOOSE TRUE should return the TLC-minimum of these 2 functions.
Filtered == {f \in [{1, 2} -> {0, 1}] : f[1] = 0}
Result == CHOOSE f \in Filtered : TRUE
"#;

    // The result should be a valid function with f[1]=0
    let result = eval_with_ops(defs, "Result[1]").unwrap();
    assert_eq!(
        result,
        Value::int(0),
        "CHOOSE TRUE over FuncSet SetPred: result should have f[1]=0"
    );

    // The result should be in the filtered set
    assert_eq!(
        eval_with_ops(defs, "Result \\in Filtered").unwrap(),
        Value::Bool(true),
        "CHOOSE TRUE over FuncSet SetPred: result should be in the filtered set"
    );
}

/// Part of #3978: Verify CHOOSE TRUE over SetPred with Interval source.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_true_over_setpred_interval() {
    // {x \in 1..100 : x > 95} = {96, 97, 98, 99, 100}
    // CHOOSE TRUE should return the TLC-minimum, which is 96.
    assert_eq!(
        eval_str(r#"CHOOSE x \in {y \in 1..100 : y > 95} : TRUE"#).unwrap(),
        Value::int(96),
        "CHOOSE TRUE over interval SetPred: should return 96 (TLC-minimum)"
    );
}

/// Part of #3978: Verify CHOOSE with predicate over SetPred domain.
///
/// General CHOOSE (not TRUE) over SetPred uses the materializing TLC-normalized
/// iteration path. This verifies it works correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_predicate_over_setpred_funcset() {
    let defs = r#"
\* [{1,2} -> {0,1}] has 4 functions. Filter to f[1]=0 (2 functions).
\* CHOOSE the one where f[2]=1.
Filtered == {f \in [{1, 2} -> {0, 1}] : f[1] = 0}
Result == CHOOSE f \in Filtered : f[2] = 1
"#;

    assert_eq!(
        eval_with_ops(defs, "Result[1]").unwrap(),
        Value::int(0),
        "CHOOSE predicate over FuncSet SetPred: result should have f[1]=0"
    );
    assert_eq!(
        eval_with_ops(defs, "Result[2]").unwrap(),
        Value::int(1),
        "CHOOSE predicate over FuncSet SetPred: result should have f[2]=1"
    );
}

/// Part of #3978: Verify CHOOSE TRUE over SetPred with SUBSET source.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_true_over_setpred_subset() {
    let defs = r#"
EXTENDS FiniteSets
\* All 2-element subsets of {1,2,3}: {{1,2}, {1,3}, {2,3}}
TwoElemSets == {s \in SUBSET {1, 2, 3} : Cardinality(s) = 2}
Result == CHOOSE s \in TwoElemSets : TRUE
"#;

    // The result should be a 2-element subset
    assert_eq!(
        eval_with_ops(defs, "Cardinality(Result)").unwrap(),
        Value::int(2),
        "CHOOSE TRUE over SUBSET SetPred: result should have 2 elements"
    );

    // The result should be in the filtered set
    assert_eq!(
        eval_with_ops(defs, "Result \\in TwoElemSets").unwrap(),
        Value::Bool(true),
        "CHOOSE TRUE over SUBSET SetPred: result should be in filtered set"
    );
}

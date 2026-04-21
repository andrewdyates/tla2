// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core TLA+ standard library operator tables.
//!
//! Operator definitions for the foundational modules: Naturals, Integers,
//! Reals, Sequences, FiniteSets, Bags, BagsExt, and TLC.

use super::OpDef;

/// Naturals module operators
/// Built-in arithmetic operators are handled by the parser/AST directly,
/// but some specs reference them by name
pub(super) const NATURALS_OPS: &[OpDef] = &[
    // The set of natural numbers (0-ary constant)
    // "Nat" is defined separately as a constant
    // Arithmetic (these are built-in syntax but can be referenced)
    // Range operator a..b is built-in
];

/// Integers module operators (extends Naturals)
pub(super) const INTEGERS_OPS: &[OpDef] = &[
    // "Int" defined separately as constant
    // Unary minus is built-in syntax
];

/// Reals module operators (extends Integers)
pub(super) const REALS_OPS: &[OpDef] = &[
    // "Real" and "Infinity" defined separately as constants
];

/// Sequences module operators
pub(super) const SEQUENCES_OPS: &[OpDef] = &[
    ("Seq", 1),    // Seq(S) - set of sequences over S
    ("Len", 1),    // Len(s) - length of sequence
    ("Head", 1),   // Head(s) - first element
    ("Tail", 1),   // Tail(s) - all but first element
    ("Append", 2), // Append(s, e) - append element
    ("SubSeq", 3), // SubSeq(s, m, n) - subsequence
    ("SelectSeq", 2), // SelectSeq(s, Test) - filter sequence
                   // \o (concatenation) is built-in syntax
];

/// FiniteSets module operators
pub(super) const FINITESETS_OPS: &[OpDef] = &[
    ("IsFiniteSet", 1), // IsFiniteSet(S) - true if S is finite
    ("Cardinality", 1), // Cardinality(S) - number of elements
];

/// Bags (multisets) module operators
pub(super) const BAGS_OPS: &[OpDef] = &[
    ("IsABag", 1),         // IsABag(B) - true if B is a bag
    ("BagToSet", 1),       // BagToSet(B) - underlying set
    ("SetToBag", 1),       // SetToBag(S) - bag with each element once
    ("BagIn", 2),          // BagIn(e, B) - true if e is in B
    ("EmptyBag", 0),       // EmptyBag - the empty bag
    ("CopiesIn", 2),       // CopiesIn(e, B) - count of e in B
    ("BagCup", 2),         // B1 (+) B2 - bag union
    ("\\oplus", 2),        // B1 (+) B2 - bag union (parenthesized operator name)
    ("BagDiff", 2),        // B1 (-) B2 - bag difference
    ("\\ominus", 2),       // B1 (-) B2 - bag difference (parenthesized operator name)
    ("BagUnion", 1),       // BagUnion(S) - bag union of set of bags
    ("SqSubseteq", 2),     // B1 \sqsubseteq B2
    ("\\sqsubseteq", 2),   // B1 \sqsubseteq B2 - bag subset (symbol name)
    ("SubBag", 1),         // SubBag(B) - set of sub-bags
    ("BagOfAll", 2),       // BagOfAll(F(_), B)
    ("BagCardinality", 1), // BagCardinality(B)
];

/// BagsExt (community) module operators
pub(super) const BAGSEXT_OPS: &[OpDef] = &[
    ("BagAdd", 2),       // BagAdd(B, e) - add one occurrence of e
    ("BagRemove", 2),    // BagRemove(B, e) - remove one occurrence of e
    ("BagRemoveAll", 2), // BagRemoveAll(B, e) - remove all occurrences of e
    ("FoldBag", 3),      // FoldBag(op, base, B)
    ("SumBag", 1),       // SumBag(B) - sum of bag elements
    ("ProductBag", 1),   // ProductBag(B) - product of bag elements
];

/// TLC module operators (model checking utilities)
pub(super) const TLC_OPS: &[OpDef] = &[
    ("Print", 2),         // Print(out, val) - print and return val
    ("PrintT", 1),        // PrintT(out) - print and return TRUE
    ("Assert", 2),        // Assert(val, out) - assert val is TRUE
    ("JavaTime", 0),      // JavaTime - current time in ms
    ("TLCGet", 1),        // TLCGet(i) - get TLC register
    ("TLCSet", 2),        // TLCSet(i, v) - set TLC register
    ("Permutations", 1),  // Permutations(S) - all permutations of S
    ("SortSeq", 2),       // SortSeq(s, Op) - sort sequence
    ("RandomElement", 1), // RandomElement(S) - random element
    ("ToString", 1),      // ToString(v) - convert to string
    ("TLCEval", 1),       // TLCEval(v) - force evaluation
    ("Any", 0),           // Any - any value (for symmetry)
                          // :> and @@ are infix operators handled specially
];

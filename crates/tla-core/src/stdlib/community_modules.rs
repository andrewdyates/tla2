// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Community module operator tables.
//!
//! Operator definitions for TLA+ community modules: Folds, Functions,
//! FiniteSetTheorems, NaturalsInduction, SequencesExt, FiniteSetsExt, TLCExt,
//! Strings, IOUtils, CSV, Json, Relation, DyadicRationals, Graphs, Bitwise,
//! Randomization, SVG, VectorClocks, and Statistics.

use super::OpDef;

/// Folds module operators (community)
/// Foundation for folding operations; used by FiniteSetsExt, Functions, SequencesExt
pub(super) const FOLDS_OPS: &[OpDef] = &[
    ("MapThenFoldSet", 5), // MapThenFoldSet(op, base, f, choose, S)
];

/// Functions module operators (community)
pub(super) const FUNCTIONS_OPS: &[OpDef] = &[
    ("Range", 1),             // Range(f) - range of function
    ("Inverse", 3),           // Inverse(f, S, T)
    ("Restrict", 2),          // Restrict(f, S) - restrict domain
    ("IsInjective", 1),       // IsInjective(f)
    ("IsSurjective", 3),      // IsSurjective(f, S, T)
    ("IsBijection", 3),       // IsBijection(f, S, T)
    ("AntiFunction", 1),      // AntiFunction(f)
    ("FoldFunction", 3),      // FoldFunction(op, base, f)
    ("FoldFunctionOnSet", 4), // FoldFunctionOnSet(op, base, f, S)
    ("RestrictDomain", 2),    // RestrictDomain(f, P) - restrict to domain elems satisfying P
    ("RestrictValues", 2),    // RestrictValues(f, P) - restrict to range elems satisfying P
    ("IsRestriction", 2),     // IsRestriction(f, g) - is f a restriction of g?
    ("Pointwise", 3),         // Pointwise(Op, f, g) - pointwise combination
];

/// FiniteSetTheorems module operators
pub(super) const FINITESETTHEOREMS_OPS: &[OpDef] = &[
    // Theorems about finite sets - mainly for TLAPS proofs
    ("FS_CardinalityType", 0),
    ("FS_EmptySet", 0),
    ("FS_Interval", 0),
    ("FS_Singleton", 0),
    ("FS_Subset", 0),
    ("FS_Union", 0),
    ("FS_SUBSET", 0),
];

/// NaturalsInduction module operators
pub(super) const NATURALSINDUCTION_OPS: &[OpDef] = &[
    // Induction principles for TLAPS
    ("NatInductiveDef", 4),
    ("NNIF", 4), // NatNonNegativeInductionDef
    ("FiniteNatInductiveDef", 4),
];

/// SequencesExt module operators (community)
pub(super) const SEQUENCESEXT_OPS: &[OpDef] = &[
    // Conversion
    ("SetToSeq", 1),     // SetToSeq(S)
    ("SetToSeqs", 1),    // SetToSeqs(S) - all permutations of set
    ("SetToSortSeq", 2), // SetToSortSeq(S, op)
    ("ToSet", 1),        // ToSet(s) - set of elements
    ("Range", 1),        // Range(s) - same as ToSet
    ("Indices", 1),      // Indices(s) - {1..Len(s)}
    // Element operations
    ("Cons", 2),     // Cons(e, s) - prepend
    ("Snoc", 2),     // Snoc(s, e) - append
    ("Front", 1),    // Front(s) - all but last
    ("Last", 1),     // Last(s)
    ("Contains", 2), // Contains(s, e)
    // Modification
    ("Reverse", 1),    // Reverse(s)
    ("Remove", 2),     // Remove(s, e)
    ("ReplaceAt", 3),  // ReplaceAt(s, i, e)
    ("InsertAt", 3),   // InsertAt(s, i, e)
    ("RemoveAt", 2),   // RemoveAt(s, i)
    ("ReplaceAll", 3), // ReplaceAll(s, old, new)
    ("Interleave", 2), // Interleave(s, t)
    // Prefix/suffix
    ("IsPrefix", 2),            // IsPrefix(s, t)
    ("IsSuffix", 2),            // IsSuffix(s, t)
    ("IsStrictPrefix", 2),      // IsStrictPrefix(s, t)
    ("IsStrictSuffix", 2),      // IsStrictSuffix(s, t)
    ("Prefixes", 1),            // Prefixes(s) - set of all prefixes
    ("Suffixes", 1),            // Suffixes(s) - set of all suffixes
    ("CommonPrefixes", 1),      // CommonPrefixes(seqs) - common prefixes of set of seqs
    ("LongestCommonPrefix", 1), // LongestCommonPrefix(seqs) - LCP of set of seqs
    // Search
    ("SelectInSeq", 2),     // SelectInSeq(s, Test) - first matching index
    ("SelectLastInSeq", 2), // SelectLastInSeq(s, Test) - last matching index
    // Combining
    ("FlattenSeq", 1), // FlattenSeq(ss) - flatten seq of seqs
    ("Zip", 2),        // Zip(s, t)
    // Fold operations
    ("FoldLeft", 3),        // FoldLeft(op, base, s)
    ("FoldRight", 3),       // FoldRight(op, s, base)
    ("FoldLeftBool", 3),    // FoldLeftBool(op, base, s)
    ("FoldRightBool", 3),   // FoldRightBool(op, s, base)
    ("FoldLeftDomain", 3),  // FoldLeftDomain(op, base, s) - fold with index
    ("FoldRightDomain", 3), // FoldRightDomain(op, s, base) - fold with index
    // Sequence generation
    ("BoundedSeq", 2), // BoundedSeq(S, n) - seqs up to length n
    ("SeqOf", 2),      // SeqOf(S, n) - alias for BoundedSeq
    ("TupleOf", 2),    // TupleOf(S, n) - tuples of exactly length n
    // Subsequences
    ("SubSeqs", 1),    // SubSeqs(s) - all contiguous subsequences
    ("AllSubSeqs", 1), // AllSubSeqs(s) - all subsequences (non-contiguous)
];

/// FiniteSetsExt module operators (community)
pub(super) const FINITESETSEXT_OPS: &[OpDef] = &[
    ("FoldSet", 3),       // FoldSet(op, base, S)
    ("ReduceSet", 3),     // ReduceSet(op, S, base)
    ("Quantify", 2),      // Quantify(S, P) - count matching
    ("Ksubsets", 2),      // Ksubsets(S, k) - k-element subsets
    ("Symmetry", 1),      // Symmetry(S)
    ("Sum", 1),           // Sum(S) - sum of set
    ("Product", 1),       // Product(S) - product of set
    ("Max", 1),           // Max(S)
    ("Min", 1),           // Min(S)
    ("Mean", 1),          // Mean(S)
    ("SymDiff", 2),       // SymDiff(S, T) - symmetric difference
    ("Flatten", 1),       // Flatten(SS) - union of sets
    ("Choose", 1),        // Choose(S) - arbitrary element
    ("MapThenSumSet", 2), // MapThenSumSet(Op, S) - map Op over S then sum
    ("Choices", 1),       // Choices(SS) - set of choice functions
    ("ChooseUnique", 2),  // ChooseUnique(S, P) - unique element satisfying P
];

/// TLCExt module operators (community)
pub(super) const TLCEXT_OPS: &[OpDef] = &[
    ("AssertError", 2),   // AssertError(msg, expr)
    ("AssertEq", 2),      // AssertEq(a, b)
    ("Trace", 0),         // Trace - get current trace
    ("TLCDefer", 1),      // TLCDefer(expr)
    ("PickSuccessor", 1), // PickSuccessor(expr)
    ("TLCNoOp", 1),       // TLCNoOp(val) - returns val unchanged
    ("TLCModelValue", 1), // TLCModelValue(str) - create model value
    ("TLCCache", 2),      // TLCCache(expr, closure) - cached evaluation
];

/// Strings module operators
pub(super) const STRINGS_OPS: &[OpDef] = &[
    ("STRING", 0), // STRING - the set of all strings
];

/// IOUtils module operators (community)
pub(super) const IOUTILS_OPS: &[OpDef] = &[
    ("IOExec", 1),            // IOExec(cmd)
    ("IOEnvExec", 2),         // IOEnvExec(env, cmd)
    ("IOExecTemplate", 2),    // IOExecTemplate(cmd, args)
    ("IOEnvExecTemplate", 3), // IOEnvExecTemplate(env, cmd, args)
    ("IOEnv", 0),             // IOEnv - all environment variables as record
    ("IOEnvGet", 1),          // IOEnvGet(var)
    ("IOEnvPut", 2),          // IOEnvPut(var, val)
    ("IODeserialize", 2),     // IODeserialize(path, default)
    ("IOSerialize", 3),       // IOSerialize(val, path, compress)
    ("Serialize", 3),         // Serialize(val, path, compress) - alias
    ("Deserialize", 2),       // Deserialize(path, default) - alias
    ("atoi", 1),              // atoi(str) - parse integer from string
    ("zeroPadN", 2),          // zeroPadN(num, n) - zero-pad integer
];

/// CSV module operators (community)
pub(super) const CSV_OPS: &[OpDef] = &[
    ("CSVRead", 3),    // CSVRead(path, header, delim)
    ("CSVRecords", 1), // CSVRecords(path)
    ("CSVWrite", 3),   // CSVWrite(records, path, header)
];

/// Json module operators (community)
pub(super) const JSON_OPS: &[OpDef] = &[
    ("JsonDeserialize", 1),   // JsonDeserialize(str)
    ("JsonSerialize", 2),     // JsonSerialize(filename, val)
    ("ndJsonDeserialize", 1), // ndJsonDeserialize(path)
    ("ndJsonSerialize", 2),   // ndJsonSerialize(records, path)
    ("ToJson", 1),            // ToJson(val) - value to JSON string
    ("ToJsonArray", 1),       // ToJsonArray(val) - sequence to JSON array string
    ("ToJsonObject", 1),      // ToJsonObject(val) - record to JSON object string
];

/// Relation module operators (community)
pub(super) const RELATION_OPS: &[OpDef] = &[
    ("IsReflexive", 2),
    ("IsReflexiveUnder", 2),
    ("IsIrreflexive", 2),
    ("IsIrreflexiveUnder", 2),
    ("IsSymmetric", 2),
    ("IsSymmetricUnder", 2),
    ("IsAntiSymmetric", 2),
    ("IsAntiSymmetricUnder", 2),
    ("IsAsymmetric", 2),
    ("IsAsymmetricUnder", 2),
    ("IsTransitive", 2),
    ("IsTransitiveUnder", 2),
    ("IsStrictlyPartiallyOrdered", 2),
    ("IsStrictlyPartiallyOrderedUnder", 2),
    ("IsPartiallyOrdered", 2),
    ("IsPartiallyOrderedUnder", 2),
    ("IsStrictlyTotallyOrdered", 2),
    ("IsStrictlyTotallyOrderedUnder", 2),
    ("IsTotallyOrdered", 2),
    ("IsTotallyOrderedUnder", 2),
    ("TransitiveClosure", 2),
    ("ReflexiveTransitiveClosure", 2),
    ("IsConnected", 2),
];

/// DyadicRationals module operators (community)
/// Dyadic rationals are fractions with denominator = 2^n
/// Represented as records [num |-> n, den |-> d]
pub(super) const DYADICRATIONALS_OPS: &[OpDef] = &[
    ("Zero", 0),             // Zero - the zero dyadic rational [num |-> 0, den |-> 1]
    ("One", 0),              // One - the one dyadic rational [num |-> 1, den |-> 1]
    ("IsDyadicRational", 1), // IsDyadicRational(r) - check if r.den is a power of 2
    ("Add", 2),              // Add(p, q) - add two dyadic rationals
    ("Half", 1),             // Half(p) - divide by 2 (double the denominator)
    ("PrettyPrint", 1),      // PrettyPrint(p) - string representation
];

/// Graphs module operators
/// Reference: ~/tlaplus/Graphs.tla (TLC CommunityModules)
pub(super) const GRAPHS_OPS: &[OpDef] = &[
    // Graph type checks
    ("IsDirectedGraph", 1),
    ("IsUndirectedGraph", 1),
    // Subgraph enumeration
    ("DirectedSubgraph", 1),
    ("UndirectedSubgraph", 1),
    // Graph transformation
    ("Transpose", 1),
    ("GraphUnion", 2),
    // Path operators
    ("Path", 1),
    ("SimplePath", 1),
    // Connectivity
    ("AreConnectedIn", 3),
    ("ConnectionsIn", 1),
    ("IsStronglyConnected", 1),
    // Structural checks
    ("IsTreeWithRoot", 2),
    ("IsBipartiteWithPartitions", 3),
    ("HasCycle", 1),
    ("IsDag", 1),
    // Node neighborhood
    ("Successors", 2),
    ("AllSuccessors", 2),
    ("Predecessors", 2),
    ("AllPredecessors", 2),
    // Transitive closure neighborhoods
    ("Ancestors", 2),
    ("Descendants", 2),
    // Degree
    ("InDegree", 2),
    ("OutDegree", 2),
    // Special node sets
    ("Roots", 1),
    ("Leaves", 1),
    // Constants and constructors
    ("EmptyGraph", 0),
    ("Graphs", 1),
];

/// UndirectedGraphs module operators
/// Note: edges are sets {a,b} not tuples <<a,b>>
pub(super) const UNDIRECTEDGRAPHS_OPS: &[OpDef] = &[
    ("IsUndirectedGraph", 1),
    ("IsLoopFreeUndirectedGraph", 1),
    ("UndirectedSubgraph", 1),
    ("Path", 1),
    ("SimplePath", 1),
    ("ConnectedComponents", 1),
    ("AreConnectedIn", 3),
    ("IsStronglyConnected", 1),
];

/// DirectedGraphs module operators
pub(super) const DIRECTEDGRAPHS_OPS: &[OpDef] = &[
    ("DirectedSubgraph", 1),
    ("SuccessorsOf", 2),
    ("PredecessorsOf", 2),
    ("Reachable", 2),
];

/// Bitwise module operators (CommunityModules)
/// Provides bitwise operations on non-negative integers
pub(super) const BITWISE_OPS: &[OpDef] = &[
    // Infix operators are defined in TLA+ as user-definable infix ops
    // a & b - bitwise AND (infix)
    ("&", 2),
    // a | b - bitwise OR (infix) - but | is already parser-handled as user-definable
    ("|", 2),
    // a ^^ b - bitwise XOR (infix)
    ("^^", 2),
    // Not(a) - bitwise NOT
    ("Not", 1),
    // shiftR(n, pos) - logical right shift
    ("shiftR", 2),
];

/// Randomization module operators (TLC standard module)
/// Provides random element/subset selection for testing
pub(super) const RANDOMIZATION_OPS: &[OpDef] = &[
    // RandomElement(S) - return a pseudo-random element from set S
    ("RandomElement", 1),
    // RandomSubset(k, S) - return a random k-element subset of S
    ("RandomSubset", 2),
    // RandomSetOfSubsets(k, n, S) - return a set of random subsets
    ("RandomSetOfSubsets", 3),
    // TestRandomSetOfSubsets is a test helper, typically not used in specs
];

/// SVG module operators (CommunityModules)
/// For animation and visualization of TLA+ specs
pub(super) const SVG_OPS: &[OpDef] = &[
    // SVGElem(name, attrs, children, innerText) - create SVG element record
    ("SVGElem", 4),
    // Line(x1, y1, x2, y2, attrs) - create line element
    ("Line", 5),
    // Circle(cx, cy, r, attrs) - create circle element
    ("Circle", 4),
    // Rect(x, y, w, h, attrs) - create rectangle element
    ("Rect", 5),
    // Text(x, y, text, attrs) - create text element
    ("Text", 4),
    // Image(x, y, width, height, href, attrs) - create image element
    ("Image", 6),
    // Group(children, attrs) - create group element
    ("Group", 2),
    // Svg(children, attrs) - create svg container
    ("Svg", 2),
    // SVGDoc(children, vbX, vbY, vbW, vbH, attrs) - create SVG document
    ("SVGDoc", 6),
    // SVGElemToString(elem) - convert element to string (built-in)
    ("SVGElemToString", 1),
    // NodeOfRingNetwork(cx, cy, r, n, m) - calculate ring network position (built-in)
    ("NodeOfRingNetwork", 5),
    // NodesOfDirectedMultiGraph(nodes, edges, options) - graph layout
    ("NodesOfDirectedMultiGraph", 3),
    // PointOnLine(from, to, segment) - interpolate point on line
    ("PointOnLine", 3),
    // SVGSerialize(svg, frameNamePrefix, frameNumber) - serialize to file
    ("SVGSerialize", 3),
];

/// VectorClocks module operators (CommunityModules)
/// For trace export and causal ordering analysis
pub(super) const VECTORCLOCKS_OPS: &[OpDef] = &[
    // IsCausalOrder(log, clock) - check if log respects causal ordering
    ("IsCausalOrder", 2),
    // CausalOrder(log, clock, node, domain) - sort log by vector clock
    ("CausalOrder", 4),
];

/// Statistics module operators (CommunityModules)
/// For statistical tests in simulation mode
pub(super) const STATISTICS_OPS: &[OpDef] = &[
    // ChiSquare(expected, observed, significance) - chi-square test
    // Returns TRUE if observed distribution matches expected at given significance
    ("ChiSquare", 3),
];

/// Apalache module operators
/// Apalache extends TLA+ with operators for symbolic model checking.
/// In BFS mode, these have concrete semantics (Gen returns {}, Guess is CHOOSE, etc.).
/// Reference: <https://apalache-mc.org/docs/lang/apalache-operators.html>
pub(super) const APALACHE_OPS: &[OpDef] = &[
    ("Gen", 1),              // Gen(n) - symbolic value generation (BFS: empty set)
    ("Guess", 1),            // Guess(S) - non-deterministic choice (BFS: CHOOSE)
    ("ApaFoldSet", 3),       // ApaFoldSet(Op, v, S) - fold binary op over set
    ("ApaFoldSeqLeft", 3),   // ApaFoldSeqLeft(Op, v, seq) - left fold over sequence
    ("Skolem", 1),           // Skolem(e) - identity (annotation hint)
    ("Expand", 1),           // Expand(S) - identity (annotation hint)
    ("ConstCardinality", 1), // ConstCardinality(e) - identity (annotation hint)
    ("MkSeq", 2),            // MkSeq(N, F) - build <<F(1), ..., F(N)>>
    ("Repeat", 3),           // Repeat(F, N, x) - apply F N times starting from x
    ("SetAsFun", 1),         // SetAsFun(S) - convert set of pairs to function
    ("FunAsSeq", 3),         // FunAsSeq(f, n, maxLen) - interpret function as sequence
];

/// Variants module operators (Apalache)
/// Tagged union (variant) values for Apalache specs.
/// Reference: <https://apalache-mc.org/docs/lang/apalache-operators.html#variants>
pub(super) const VARIANTS_OPS: &[OpDef] = &[
    ("Variant", 2),          // Variant(tag, value) - create tagged union
    ("VariantTag", 1),       // VariantTag(v) - extract tag string
    ("VariantGetUnsafe", 2), // VariantGetUnsafe(tag, v) - extract value (error on mismatch)
    ("VariantGetOrElse", 3), // VariantGetOrElse(tag, v, default) - extract with default
    ("VariantFilter", 2),    // VariantFilter(tag, S) - filter set of variants by tag
    ("UNIT", 0),             // UNIT - the unit value "U_OF_UNIT"
];

/// Option module operators (Apalache)
/// Option types built on Variants: Some(a) | None(UNIT).
/// Reference: <https://apalache-mc.org/docs/lang/apalache-operators.html>
pub(super) const OPTION_OPS: &[OpDef] = &[
    ("Some", 1),             // Some(val) - wrap value in Some variant
    ("None", 0),             // None - the None variant (tag "None", value UNIT)
    ("IsSome", 1),           // IsSome(opt) - check if variant has tag "Some"
    ("IsNone", 1),           // IsNone(opt) - check if variant has tag "None"
    ("OptionCase", 3),       // OptionCase(opt, someFn, noneFn) - pattern match
    ("OptionMap", 2),        // OptionMap(opt, fn) - map over Some value
    ("OptionFlatMap", 2),    // OptionFlatMap(opt, fn) - flatMap over Some value
    ("OptionGetOrElse", 2),  // OptionGetOrElse(opt, default) - extract or default
    ("OptionToSeq", 1),      // OptionToSeq(opt) - Some(x) -> <<x>>, None -> <<>>
    ("OptionToSet", 1),      // OptionToSet(opt) - Some(x) -> {x}, None -> {}
    ("OptionGuess", 1),      // OptionGuess(set) - pick from set as Option
    ("OptionFunApp", 2),     // OptionFunApp(fn, key) - safe function application
    ("OptionPartialFun", 2), // OptionPartialFun(fn, dom) - partial function wrapper
];

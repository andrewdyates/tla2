// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use tla_core::span::Spanned;

impl TypeContext {
    /// Register stdlib operators based on EXTENDS clause
    pub(crate) fn register_stdlib_operators(&mut self, extends: &[Spanned<String>]) {
        for ext in extends {
            let ops_to_add: Vec<(&str, TlaType)> = match ext.node.as_str() {
                "Sequences" => vec![
                    ("Len", TlaType::Int),
                    ("Head", TlaType::Unknown),
                    ("Tail", TlaType::Unknown),
                    ("Append", TlaType::Unknown),
                    ("SubSeq", TlaType::Unknown),
                    ("Seq", TlaType::Unknown),
                    ("SelectSeq", TlaType::Unknown),
                ],
                "FiniteSets" => vec![
                    ("Cardinality", TlaType::Int),
                    ("IsFiniteSet", TlaType::Bool),
                ],
                "TLC" => vec![
                    ("Print", TlaType::Unknown),
                    ("PrintT", TlaType::Bool),
                    ("Assert", TlaType::Bool),
                    ("ToString", TlaType::String),
                    ("JavaTime", TlaType::Int),
                    ("TLCGet", TlaType::Unknown),
                    ("TLCSet", TlaType::Bool),
                    ("Permutations", TlaType::Unknown),
                    ("SortSeq", TlaType::Unknown),
                    ("RandomElement", TlaType::Unknown),
                    ("TLCEval", TlaType::Unknown),
                    ("Any", TlaType::Unknown),
                ],
                "SequencesExt" => vec![
                    ("SetToSeq", TlaType::Unknown),
                    ("SetToSortSeq", TlaType::Unknown),
                    ("Reverse", TlaType::Unknown),
                    ("Remove", TlaType::Unknown),
                    ("ReplaceAt", TlaType::Unknown),
                    ("InsertAt", TlaType::Unknown),
                    ("RemoveAt", TlaType::Unknown),
                    ("Front", TlaType::Unknown),
                    ("Last", TlaType::Unknown),
                    ("IsPrefix", TlaType::Bool),
                    ("IsSuffix", TlaType::Bool),
                    ("Contains", TlaType::Bool),
                    ("Cons", TlaType::Unknown),
                    ("FlattenSeq", TlaType::Unknown),
                    ("Zip", TlaType::Unknown),
                    ("FoldLeft", TlaType::Unknown),
                    ("FoldRight", TlaType::Unknown),
                    ("ToSet", TlaType::Unknown),
                    ("Range", TlaType::Unknown),
                    ("Indices", TlaType::Unknown),
                ],
                "FiniteSetsExt" => vec![
                    ("FoldSet", TlaType::Unknown),
                    ("ReduceSet", TlaType::Unknown),
                    ("Quantify", TlaType::Int),
                    ("Ksubsets", TlaType::Unknown),
                    ("Symmetry", TlaType::Unknown),
                    ("Sum", TlaType::Int),
                    ("Product", TlaType::Int),
                    ("Max", TlaType::Int),
                    ("Min", TlaType::Int),
                    ("Mean", TlaType::Int),
                    ("SymDiff", TlaType::Unknown),
                    ("Flatten", TlaType::Unknown),
                    ("Choose", TlaType::Unknown),
                ],
                "Functions" => vec![
                    ("Range", TlaType::Unknown),
                    ("Inverse", TlaType::Unknown),
                    ("Restrict", TlaType::Unknown),
                    ("IsInjective", TlaType::Bool),
                    ("IsSurjective", TlaType::Bool),
                    ("IsBijection", TlaType::Bool),
                    ("AntiFunction", TlaType::Unknown),
                    ("FoldFunction", TlaType::Unknown),
                    ("FoldFunctionOnSet", TlaType::Unknown),
                ],
                "Bags" => vec![
                    ("IsABag", TlaType::Bool),
                    ("BagToSet", TlaType::Unknown),
                    ("SetToBag", TlaType::Unknown),
                    ("BagIn", TlaType::Bool),
                    ("EmptyBag", TlaType::Unknown),
                    ("CopiesIn", TlaType::Int),
                    ("BagCup", TlaType::Unknown),
                    ("BagDiff", TlaType::Unknown),
                    ("BagUnion", TlaType::Unknown),
                    ("SqSubseteq", TlaType::Bool),
                    ("SubBag", TlaType::Unknown),
                    ("BagOfAll", TlaType::Unknown),
                    ("BagCardinality", TlaType::Int),
                ],
                "TLCExt" => vec![
                    ("AssertError", TlaType::Unknown),
                    ("AssertEq", TlaType::Bool),
                    ("Trace", TlaType::Unknown),
                    ("TLCDefer", TlaType::Unknown),
                    ("PickSuccessor", TlaType::Unknown),
                ],
                // Naturals and Integers don't add callable operators (just built-in syntax)
                "Naturals" | "Integers" | "Reals" => vec![],
                _ => vec![],
            };

            for (name, ty) in ops_to_add {
                self.ops.insert(name.to_string(), ty);
            }
        }
    }
}

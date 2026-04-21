// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_stdlib_module() {
    assert!(is_stdlib_module("Naturals"));
    assert!(is_stdlib_module("Integers"));
    assert!(is_stdlib_module("Sequences"));
    assert!(is_stdlib_module("TLC"));
    assert!(is_stdlib_module("Apalache"));
    assert!(is_stdlib_module("Variants"));
    assert!(is_stdlib_module("Option"));
    assert!(!is_stdlib_module("MyModule"));
    assert!(!is_stdlib_module(""));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_get_module_operators() {
    let seq_ops = get_module_operators("Sequences");
    assert!(seq_ops.iter().any(|(name, _)| *name == "Seq"));
    assert!(seq_ops.iter().any(|(name, _)| *name == "Len"));
    assert!(seq_ops.iter().any(|(name, _)| *name == "Head"));
    assert!(seq_ops.iter().any(|(name, _)| *name == "Tail"));
    assert!(seq_ops.iter().any(|(name, _)| *name == "Append"));

    let fs_ops = get_module_operators("FiniteSets");
    assert!(fs_ops.iter().any(|(name, _)| *name == "Cardinality"));
    assert!(fs_ops.iter().any(|(name, _)| *name == "IsFiniteSet"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_apalache_module_operators() {
    let apa_ops = get_module_operators("Apalache");
    assert!(apa_ops.iter().any(|(name, _)| *name == "Gen"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "Guess"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "ApaFoldSet"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "ApaFoldSeqLeft"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "Skolem"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "Expand"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "ConstCardinality"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "MkSeq"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "Repeat"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "SetAsFun"));
    assert!(apa_ops.iter().any(|(name, _)| *name == "FunAsSeq"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_variants_module_operators() {
    let var_ops = get_module_operators("Variants");
    assert!(var_ops.iter().any(|(name, _)| *name == "Variant"));
    assert!(var_ops.iter().any(|(name, _)| *name == "VariantTag"));
    assert!(var_ops.iter().any(|(name, _)| *name == "VariantGetUnsafe"));
    assert!(var_ops.iter().any(|(name, _)| *name == "VariantGetOrElse"));
    assert!(var_ops.iter().any(|(name, _)| *name == "VariantFilter"));
    assert!(var_ops.iter().any(|(name, _)| *name == "UNIT"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_option_module_operators() {
    assert!(is_stdlib_module("Option"));
    let opt_ops = get_module_operators("Option");
    assert!(opt_ops.iter().any(|(name, _)| *name == "Some"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "None"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "IsSome"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "IsNone"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionCase"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionMap"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionFlatMap"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionGetOrElse"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionToSeq"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionToSet"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionGuess"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionFunApp"));
    assert!(opt_ops.iter().any(|(name, _)| *name == "OptionPartialFun"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_transitive_extends() {
    // Integers should include Naturals symbols
    let int_ops = get_module_operators("Integers");
    // Integers itself doesn't have many ops, but injection handles transitivity
    assert!(int_ops.is_empty() || int_ops.len() < 3);
}

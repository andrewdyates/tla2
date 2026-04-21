// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1909: function construction over SUBSET-backed SetPred
/// domains must eagerly enumerate the domain when finite.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_function_construction_over_subset_setpred_domain() {
    let defs = r#"
EXTENDS FiniteSets
S == {s \in SUBSET {1, 2} : Cardinality(s) = 1}
F == [x \in S |-> Cardinality(x)]
"#;
    assert_eq!(eval_with_ops(defs, "F[{1}]").unwrap(), Value::int(1));
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for constant value parsing

use super::parse::*;
use crate::value::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_integer() {
    assert_eq!(parse_constant_value("3").unwrap(), Value::int(3));
    assert_eq!(parse_constant_value("-42").unwrap(), Value::int(-42));
    assert_eq!(parse_constant_value("  100  ").unwrap(), Value::int(100));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_model_value() {
    assert_eq!(
        parse_constant_value("foo").unwrap(),
        Value::try_model_value("foo").unwrap()
    );
    assert_eq!(
        parse_constant_value("server1").unwrap(),
        Value::try_model_value("server1").unwrap()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_empty_set() {
    assert_eq!(parse_constant_value("{}").unwrap(), Value::empty_set());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_integer_set() {
    let result = parse_constant_value("{1, 2, 3}").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 3);
        assert!(set.contains(&Value::int(1)));
        assert!(set.contains(&Value::int(2)));
        assert!(set.contains(&Value::int(3)));
    } else {
        panic!("Expected set");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_model_value_set() {
    let result = parse_constant_value("{matches, paper, tobacco}").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 3);
        assert!(set.contains(&Value::try_model_value("matches").unwrap()));
        assert!(set.contains(&Value::try_model_value("paper").unwrap()));
        assert!(set.contains(&Value::try_model_value("tobacco").unwrap()));
    } else {
        panic!("Expected set");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_nested_set() {
    let result = parse_constant_value("{{a, b}, {c, d}}").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 2);
    } else {
        panic!("Expected set");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_tuple() {
    let result = parse_constant_value("<<1, 2, 3>>").unwrap();
    if let Value::Tuple(ref tuple) = result {
        assert_eq!(tuple.len(), 3);
        assert_eq!(tuple[0], Value::int(1));
    } else {
        panic!("Expected tuple");
    }
}

// ==================== New tests for Z4 Integration (Phase 9) ====================

/// Part of #3287: Verify that parse_constant_value routes string literals
/// through intern_string(), assigning TLC tokens at parse time rather than
/// deferring to first comparison.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_string_literal_assigns_tlc_token_at_parse_time() {
    use crate::value::tlc_string_token;

    // Use unique prefix to avoid interference from concurrent tests
    let prefix = "parse_const_3287_";
    let input = format!("\"{prefix}hello\"");
    let val = parse_constant_value(&input).unwrap();
    let Value::String(arc) = &val else {
        panic!("Expected Value::String, got {val:?}");
    };

    // Token should already be assigned by parse_constant_value → Value::string → intern_string
    let tok = tlc_string_token(arc);
    assert_ne!(
        tok, 0,
        "Parsed string literal should have eager TLC token, got 0"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_string_literal() {
    assert_eq!(
        parse_constant_value("\"hello\"").unwrap(),
        Value::String("hello".into())
    );
    assert_eq!(
        parse_constant_value("\"neg\"").unwrap(),
        Value::String("neg".into())
    );
    assert_eq!(
        parse_constant_value("\"SAT\"").unwrap(),
        Value::String("SAT".into())
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_boolean_literal() {
    assert_eq!(parse_constant_value("TRUE").unwrap(), Value::Bool(true));
    assert_eq!(parse_constant_value("FALSE").unwrap(), Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_tuple_with_string() {
    // Z4 use case: <<v1, "neg">>
    let result = parse_constant_value("<<v1, \"neg\">>").unwrap();
    if let Value::Tuple(ref tuple) = result {
        assert_eq!(tuple.len(), 2);
        assert_eq!(tuple[0], Value::try_model_value("v1").unwrap());
        assert_eq!(tuple[1], Value::String("neg".into()));
    } else {
        panic!("Expected tuple, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_record_simple() {
    let result = parse_constant_value("[x |-> 1]").unwrap();
    let rec = result.as_record().unwrap();
    assert_eq!(rec.len(), 1);
    assert_eq!(rec.get(&std::sync::Arc::from("x")), Some(&Value::int(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_record_multiple_fields() {
    let result = parse_constant_value("[x |-> 1, y |-> 2, z |-> 3]").unwrap();
    let rec = result.as_record().unwrap();
    assert_eq!(rec.len(), 3);
    assert_eq!(rec.get(&std::sync::Arc::from("x")), Some(&Value::int(1)));
    assert_eq!(rec.get(&std::sync::Arc::from("y")), Some(&Value::int(2)));
    assert_eq!(rec.get(&std::sync::Arc::from("z")), Some(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_record_with_string_value() {
    let result = parse_constant_value("[status |-> \"active\"]").unwrap();
    let rec = result.as_record().unwrap();
    assert_eq!(
        rec.get(&std::sync::Arc::from("status")),
        Some(&Value::String("active".into()))
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_set_of_tuples_with_strings() {
    // Z4 use case: {<<v1, "neg">>, <<v2, "pos">>}
    let result = parse_constant_value("{<<v1, \"neg\">>, <<v2, \"pos\">>}").unwrap();
    if let Value::Set(ref set) = result {
        assert_eq!(set.len(), 2);
    } else {
        panic!("Expected set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_z4_cdcl_clauses() {
    // Full Z4 use case: sets of sets of tuples with strings
    // Clauses = { {<<v1, "pos">>, <<v2, "pos">>}, {<<v1, "neg">>}, {<<v2, "neg">>} }
    let input = "{ {<<v1, \"pos\">>, <<v2, \"pos\">>}, {<<v1, \"neg\">>}, {<<v2, \"neg\">>} }";
    let result = parse_constant_value(input).unwrap();

    if let Value::Set(ref clauses) = result {
        assert_eq!(clauses.len(), 3);

        // Check that we have sets of tuples
        for clause in clauses.iter() {
            if let Value::Set(ref literals) = clause {
                for lit in literals.iter() {
                    if let Value::Tuple(ref tuple) = lit {
                        assert_eq!(tuple.len(), 2);
                        // First element is model value (variable)
                        assert!(matches!(tuple[0], Value::ModelValue(_)));
                        // Second element is string (polarity)
                        assert!(matches!(tuple[1], Value::String(_)));
                    } else {
                        panic!("Expected tuple in clause, got {:?}", lit);
                    }
                }
            } else {
                panic!("Expected set of literals, got {:?}", clause);
            }
        }
    } else {
        panic!("Expected set of clauses, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_nested_record_in_set() {
    // Edges = { [src |-> n1, dst |-> n2, weight |-> 5], [src |-> n2, dst |-> n3, weight |-> 3] }
    let input =
        "{ [src |-> n1, dst |-> n2, weight |-> 5], [src |-> n2, dst |-> n3, weight |-> 3] }";
    let result = parse_constant_value(input).unwrap();

    if let Value::Set(ref edges) = result {
        assert_eq!(edges.len(), 2);
        for edge in edges.iter() {
            let rec = edge.as_record().expect("Expected record for edge");
            assert!(rec.contains_key(&std::sync::Arc::from("src")));
            assert!(rec.contains_key(&std::sync::Arc::from("dst")));
            assert!(rec.contains_key(&std::sync::Arc::from("weight")));
        }
    } else {
        panic!("Expected set of records, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_string_with_comma() {
    // Edge case: string containing comma shouldn't split
    let result = parse_constant_value("\"hello, world\"").unwrap();
    assert_eq!(result, Value::String("hello, world".into()));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_tuple_with_string_containing_comma() {
    let result = parse_constant_value("<<a, \"b, c\">>").unwrap();
    if let Value::Tuple(ref tuple) = result {
        assert_eq!(tuple.len(), 2);
        assert_eq!(tuple[0], Value::try_model_value("a").unwrap());
        assert_eq!(tuple[1], Value::String("b, c".into()));
    } else {
        panic!("Expected tuple, got {:?}", result);
    }
}

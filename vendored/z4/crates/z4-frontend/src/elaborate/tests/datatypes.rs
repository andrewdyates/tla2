// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_declare_datatype_simple() {
    let mut ctx = Context::new();

    let script = "(declare-datatype Color ((Red) (Green) (Blue)))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert!(ctx.sort_defs.contains_key("Color"));

    let red = ctx.symbols.get("Red").expect("Red constructor not found");
    assert!(red.arg_sorts.is_empty());
    assert!(red.term.is_some());

    let green = ctx
        .symbols
        .get("Green")
        .expect("Green constructor not found");
    assert!(green.arg_sorts.is_empty());

    let blue = ctx.symbols.get("Blue").expect("Blue constructor not found");
    assert!(blue.arg_sorts.is_empty());

    let is_red = ctx.symbols.get("is-Red").expect("is-Red tester not found");
    assert_eq!(is_red.arg_sorts.len(), 1);
    assert_eq!(is_red.sort, Sort::Bool);

    let is_green = ctx
        .symbols
        .get("is-Green")
        .expect("is-Green tester not found");
    assert_eq!(is_green.arg_sorts.len(), 1);
    assert_eq!(is_green.sort, Sort::Bool);
}

#[test]
fn test_declare_datatype_with_selectors() {
    let mut ctx = Context::new();

    let script = "(declare-datatype Point ((mk-point (x Int) (y Int))))";
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert!(ctx.sort_defs.contains_key("Point"));

    let mk_point = ctx
        .symbols
        .get("mk-point")
        .expect("mk-point constructor not found");
    assert_eq!(mk_point.arg_sorts.len(), 2);
    assert_eq!(mk_point.arg_sorts[0], Sort::Int);
    assert_eq!(mk_point.arg_sorts[1], Sort::Int);
    assert!(mk_point.term.is_none());

    let sel_x = ctx.symbols.get("x").expect("x selector not found");
    assert_eq!(sel_x.arg_sorts.len(), 1);
    assert_eq!(sel_x.sort, Sort::Int);

    let sel_y = ctx.symbols.get("y").expect("y selector not found");
    assert_eq!(sel_y.arg_sorts.len(), 1);
    assert_eq!(sel_y.sort, Sort::Int);

    let is_mk_point = ctx
        .symbols
        .get("is-mk-point")
        .expect("is-mk-point tester not found");
    assert_eq!(is_mk_point.arg_sorts.len(), 1);
    assert_eq!(is_mk_point.sort, Sort::Bool);
}

#[test]
fn test_declare_datatypes_mutually_recursive() {
    let mut ctx = Context::new();

    let script = r#"(declare-datatypes ((Tree 0) (Forest 0))
                        (((leaf (val Int)) (node (children Forest)))
                         ((nil) (cons (head Tree) (tail Forest)))))"#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert!(ctx.sort_defs.contains_key("Tree"));
    assert!(ctx.sort_defs.contains_key("Forest"));

    let leaf = ctx.symbols.get("leaf").expect("leaf constructor not found");
    assert_eq!(leaf.arg_sorts.len(), 1);
    assert_eq!(leaf.arg_sorts[0], Sort::Int);

    let node = ctx.symbols.get("node").expect("node constructor not found");
    assert_eq!(node.arg_sorts.len(), 1);
    assert_eq!(node.arg_sorts[0], Sort::Uninterpreted("Forest".to_string()));

    let nil = ctx.symbols.get("nil").expect("nil constructor not found");
    assert!(nil.arg_sorts.is_empty());
    assert!(nil.term.is_some());

    let cons = ctx.symbols.get("cons").expect("cons constructor not found");
    assert_eq!(cons.arg_sorts.len(), 2);
    assert_eq!(cons.arg_sorts[0], Sort::Uninterpreted("Tree".to_string()));
    assert_eq!(cons.arg_sorts[1], Sort::Uninterpreted("Forest".to_string()));

    let head = ctx.symbols.get("head").expect("head selector not found");
    assert_eq!(head.sort, Sort::Uninterpreted("Tree".to_string()));

    let tail = ctx.symbols.get("tail").expect("tail selector not found");
    assert_eq!(tail.sort, Sort::Uninterpreted("Forest".to_string()));
}

#[test]
fn test_declare_datatype_can_use_in_terms() {
    let mut ctx = Context::new();

    let script = r#"
            (declare-datatype Option ((None) (Some (value Int))))
            (declare-const x Option)
            (assert (is-Some x))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

/// Test for #1190: SMT-LIB standard datatype tester syntax ((_ is Ctor) x)
/// This is the standard form; z4 registers testers as "is-Ctor" internally.
#[test]
fn test_datatype_tester_standard_syntax_1190() {
    let mut ctx = Context::new();

    let script = r#"
            (declare-datatype Option ((None) (Some (value Int))))
            (declare-const x Option)
            (assert ((_ is Some) x))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_datatype_overloaded_selectors_resolve_by_argument_sort() {
    let mut ctx = Context::new();

    let script = r#"
            (declare-datatype Inner ((Inner_mk (fld_0 (_ BitVec 8)) (fld_1 Bool))))
            (declare-datatype Outer ((Outer_mk (fld_0 Inner) (fld_1 (_ BitVec 8)))))
            (assert (= (concat (fld_0 (fld_0 (Outer_mk (Inner_mk #x2a true) #x07))) #x07) #x2a07))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
    assert_eq!(*ctx.terms.sort(ctx.assertions[0]), Sort::Bool);
}

/// Test for #1729: datatype_iter() and is_constructor() accessor methods
#[test]
fn test_datatype_iter_and_is_constructor() {
    let mut ctx = Context::new();

    // Declare Color enum and Option type
    let script = r#"
            (declare-datatype Color ((Red) (Green) (Blue)))
            (declare-datatype Option ((None) (Some (value Int))))
        "#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Test datatype_iter: should yield both datatypes
    let datatypes: Vec<_> = ctx.datatype_iter().collect();
    assert_eq!(datatypes.len(), 2);

    // Check Color constructors
    let color_entry = datatypes.iter().find(|(name, _)| *name == "Color");
    assert!(color_entry.is_some());
    let (_, color_ctors) = color_entry.unwrap();
    assert_eq!(color_ctors.len(), 3);
    assert!(color_ctors.contains(&"Red".to_string()));
    assert!(color_ctors.contains(&"Green".to_string()));
    assert!(color_ctors.contains(&"Blue".to_string()));

    // Check Option constructors
    let option_entry = datatypes.iter().find(|(name, _)| *name == "Option");
    assert!(option_entry.is_some());
    let (_, option_ctors) = option_entry.unwrap();
    assert_eq!(option_ctors.len(), 2);
    assert!(option_ctors.contains(&"None".to_string()));
    assert!(option_ctors.contains(&"Some".to_string()));

    // Test is_constructor: constructors return Some((dt_name, ctor_name))
    assert_eq!(
        ctx.is_constructor("Red"),
        Some(("Color".to_string(), "Red".to_string()))
    );
    assert_eq!(
        ctx.is_constructor("Some"),
        Some(("Option".to_string(), "Some".to_string()))
    );

    // Non-constructors return None
    assert_eq!(ctx.is_constructor("NotAConstructor"), None);
    assert_eq!(ctx.is_constructor("value"), None); // selector, not constructor
}

/// Test push/pop correctly scopes datatypes and constructors
#[test]
fn test_datatype_push_pop_scoping() {
    let mut ctx = Context::new();

    // Declare Color at top level
    let script1 = "(declare-datatype Color ((Red) (Green) (Blue)))";
    for cmd in parse(script1).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Verify Color is visible
    assert_eq!(ctx.datatype_iter().count(), 1);
    assert!(ctx.is_constructor("Red").is_some());

    // Push a scope and declare Option inside it
    ctx.push();
    let script2 = "(declare-datatype Option ((None) (Some (value Int))))";
    for cmd in parse(script2).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Both datatypes should be visible
    assert_eq!(ctx.datatype_iter().count(), 2);
    assert!(ctx.is_constructor("Red").is_some());
    assert!(ctx.is_constructor("None").is_some());
    assert!(ctx.is_constructor("Some").is_some());

    // Pop the scope
    assert!(ctx.pop(), "pop should succeed after push");

    // Only Color should remain, Option and its constructors should be gone
    assert_eq!(ctx.datatype_iter().count(), 1);
    assert!(ctx.is_constructor("Red").is_some());
    assert!(ctx.is_constructor("None").is_none());
    assert!(ctx.is_constructor("Some").is_none());

    // Verify symbols are also scoped (constructors, selectors, testers)
    assert!(ctx.symbols.contains_key("Red")); // Color constructor still exists
    assert!(ctx.symbols.contains_key("is-Red")); // Color tester still exists
    assert!(!ctx.symbols.contains_key("None")); // Option constructor gone
    assert!(!ctx.symbols.contains_key("Some")); // Option constructor gone
    assert!(!ctx.symbols.contains_key("value")); // Option selector gone
    assert!(!ctx.symbols.contains_key("is-None")); // Option tester gone
    assert!(!ctx.symbols.contains_key("is-Some")); // Option tester gone

    // Verify sort_defs are also scoped
    assert!(ctx.sort_defs.contains_key("Color")); // Color sort still exists
    assert!(!ctx.sort_defs.contains_key("Option")); // Option sort gone
}

/// Test datatype_iter and is_constructor work with declare-datatypes (mutually recursive)
#[test]
fn test_datatype_iter_with_declare_datatypes() {
    let mut ctx = Context::new();

    // Declare mutually recursive Tree/Forest types
    let script = r#"(declare-datatypes ((Tree 0) (Forest 0))
                        (((leaf (val Int)) (node (children Forest)))
                         ((nil) (cons (head Tree) (tail Forest)))))"#;
    for cmd in parse(script).unwrap() {
        ctx.process_command(&cmd).unwrap();
    }

    // Test datatype_iter: should yield both datatypes
    let datatypes: Vec<_> = ctx.datatype_iter().collect();
    assert_eq!(datatypes.len(), 2);

    // Check Tree exists with correct constructors
    let tree_entry = datatypes.iter().find(|(name, _)| *name == "Tree");
    assert!(tree_entry.is_some());
    let (_, tree_ctors) = tree_entry.unwrap();
    assert_eq!(tree_ctors.len(), 2);
    assert!(tree_ctors.contains(&"leaf".to_string()));
    assert!(tree_ctors.contains(&"node".to_string()));

    // Check Forest exists with correct constructors
    let forest_entry = datatypes.iter().find(|(name, _)| *name == "Forest");
    assert!(forest_entry.is_some());
    let (_, forest_ctors) = forest_entry.unwrap();
    assert_eq!(forest_ctors.len(), 2);
    assert!(forest_ctors.contains(&"nil".to_string()));
    assert!(forest_ctors.contains(&"cons".to_string()));

    // Test is_constructor works for mutually recursive constructors
    assert_eq!(
        ctx.is_constructor("leaf"),
        Some(("Tree".to_string(), "leaf".to_string()))
    );
    assert_eq!(
        ctx.is_constructor("cons"),
        Some(("Forest".to_string(), "cons".to_string()))
    );
}

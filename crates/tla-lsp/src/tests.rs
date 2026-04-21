// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tower_lsp::lsp_types::*;

use crate::analysis::SemanticDiagnosticKind;
use crate::document::DocumentState;
use crate::{completions, position, symbols};

const TEST_MODULE: &str = r#"
---- MODULE Test ----
EXTENDS Naturals, Sequences

VARIABLE x, y
CONSTANT N

Init == x = 0 /\ y = 0

Inc(n) == x' = x + n /\ y' = y

Next == Inc(1) \/ Inc(2)

Spec == Init /\ [][Next]_<<x, y>>
====
"#;

const SYMBOL_UNITS_MODULE: &str = r#"
---- MODULE SymbolKinds ----
EXTENDS Naturals, Sequences

VARIABLE x
RECURSIVE F(_)

F(n) == IF n = 0 THEN 0 ELSE F(n - 1)

INSTANCE Sequences

ASSUME x \in Nat

THEOREM T1 == x = x
====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_offset_to_position() {
    let source = "line1\nline2\nline3";
    // Position at start of line2
    let pos = position::offset_to_position(source, 6);
    assert_eq!(pos.line, 1);
    assert_eq!(pos.character, 0);

    // Position in middle of line2
    let pos = position::offset_to_position(source, 8);
    assert_eq!(pos.line, 1);
    assert_eq!(pos.character, 2);

    // Position at start
    let pos = position::offset_to_position(source, 0);
    assert_eq!(pos.line, 0);
    assert_eq!(pos.character, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_position_to_offset() {
    let source = "line1\nline2\nline3";
    // Start of line2
    let offset = position::position_to_offset(source, Position::new(1, 0));
    assert_eq!(offset, 6);

    // Character 2 of line2
    let offset = position::position_to_offset(source, Position::new(1, 2));
    assert_eq!(offset, 8);

    // Start of file
    let offset = position::position_to_offset(source, Position::new(0, 0));
    assert_eq!(offset, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_keyword_completions() {
    let completions = completions::get_keyword_completions();
    let labels: Vec<_> = completions.iter().map(|c| c.label.as_str()).collect();

    // Check for essential keywords
    for kw in &[
        "MODULE", "EXTENDS", "VARIABLE", "CONSTANT", "THEOREM", "LET", "IF", "CHOOSE",
    ] {
        assert!(
            labels.contains(kw),
            "keyword completion missing '{}', got: {:?}",
            kw,
            labels
        );
    }

    // Check all items have KEYWORD kind
    for item in &completions {
        assert_eq!(item.kind, Some(CompletionItemKind::KEYWORD));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_module_completions() {
    let completions = completions::get_stdlib_module_completions();
    let labels: Vec<_> = completions.iter().map(|c| c.label.as_str()).collect();

    // Check for common stdlib modules
    for module in &["Naturals", "Integers", "Sequences", "FiniteSets", "TLC"] {
        assert!(
            labels.contains(module),
            "stdlib module completion missing '{}', got: {:?}",
            module,
            labels
        );
    }

    // Check all items have MODULE kind
    for item in &completions {
        assert_eq!(item.kind, Some(CompletionItemKind::MODULE));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_document_state_analyze() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    // Should parse successfully
    assert!(doc.parse_errors.is_empty());
    assert!(doc.lower_errors.is_empty());
    assert!(doc.module.is_some());
    assert!(doc.resolve.is_some());

    let module = doc
        .module
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");
    assert_eq!(module.name.node, "Test");

    // Check EXTENDS — exact list
    let extends: Vec<_> = module.extends.iter().map(|e| e.node.as_str()).collect();
    assert_eq!(
        extends,
        vec!["Naturals", "Sequences"],
        "expected EXTENDS Naturals, Sequences in order"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_document_state_analyze_empty_document() {
    let mut doc = DocumentState::new(String::new());
    doc.analyze();

    // Parser follows SANY: non-module content (including empty) produces no
    // parse error — the module is simply absent.
    assert!(doc.module.is_none(), "empty document should have no module");
    assert!(
        doc.resolve.is_none(),
        "empty document should have no resolve"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_document_symbols() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let module = doc
        .module
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");
    let syms = symbols::get_document_symbols(module, &doc.source);

    let names: Vec<_> = syms.iter().map(|s| s.name.as_str()).collect();

    // Check all expected symbols present with failure context
    for expected in &["x", "y", "N", "Init", "Inc", "Next", "Spec"] {
        assert!(
            names.contains(expected),
            "document symbol '{}' missing, got: {:?}",
            expected,
            names
        );
    }

    // Verify exact count — no phantom symbols
    assert_eq!(
        names.len(),
        7,
        "expected exactly 7 document symbols (x, y, N, Init, Inc, Next, Spec), got {}: {:?}",
        names.len(),
        names
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_local_symbol_completions() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let resolve = doc
        .resolve
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");
    let completions = completions::get_local_symbol_completions(resolve);
    let labels: Vec<_> = completions.iter().map(|c| c.label.as_str()).collect();

    // Variables, constants, and operators
    for expected in &["x", "y", "N", "Init", "Inc", "Next", "Spec"] {
        assert!(
            labels.contains(expected),
            "local symbol completion missing '{}', got: {:?}",
            expected,
            labels
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_stdlib_operator_completions() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let module = doc
        .module
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");
    let completions = completions::get_stdlib_operator_completions(module);
    let labels: Vec<_> = completions.iter().map(|c| c.label.as_str()).collect();

    // Operators from Naturals and Sequences (both extended)
    for op in &["Nat", "Seq", "Len", "Head", "Tail", "Append"] {
        assert!(
            labels.contains(op),
            "stdlib operator completion missing '{}', got: {:?}",
            op,
            labels
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hover_info() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let resolve = doc
        .resolve
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");

    // Find the Init operator definition
    let init_sym = resolve
        .symbols
        .iter()
        .find(|s| s.name == "Init")
        .expect("Init should be defined");

    let info = symbols::get_hover_info(resolve, init_sym.def_span.start + 1)
        .expect("invariant: Init symbol should have hover info");
    assert!(
        info.contains("OPERATOR"),
        "hover info for Init should contain 'OPERATOR', got: {}",
        info
    );
    assert!(
        info.contains("Init"),
        "hover info should contain 'Init', got: {}",
        info
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hover_info_on_reference_position() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let resolve = doc
        .resolve
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");

    let x_def_span = resolve
        .symbols
        .iter()
        .find(|s| s.name == "x")
        .expect("x should be defined")
        .def_span;

    let (x_use_span, _) = resolve
        .references
        .iter()
        .find(|(_, def_span)| *def_span == x_def_span)
        .expect("x should have at least one use span");

    let ref_info = symbols::get_hover_info(resolve, x_use_span.start + 1)
        .expect("hover info should be available on x reference");
    let def_info = symbols::get_hover_info(resolve, x_def_span.start + 1)
        .expect("hover info should be available on x definition");

    assert_eq!(
        ref_info, def_info,
        "hover on reference and definition should produce identical info"
    );
    assert!(
        ref_info.contains("VARIABLE"),
        "hover info for x should contain 'VARIABLE', got: {}",
        ref_info
    );
    assert!(
        ref_info.contains("x"),
        "hover info should contain 'x', got: {}",
        ref_info
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_document_symbols_extended_unit_types() {
    let mut doc = DocumentState::new(SYMBOL_UNITS_MODULE.to_string());
    doc.analyze();

    assert!(
        doc.parse_errors.is_empty(),
        "symbol-units fixture should parse cleanly: {:?}",
        doc.parse_errors
    );
    assert!(
        doc.lower_errors.is_empty(),
        "symbol-units fixture should lower cleanly: {:?}",
        doc.lower_errors
    );

    let module = doc
        .module
        .as_ref()
        .expect("invariant: SYMBOL_UNITS_MODULE should resolve to a module");
    let syms = symbols::get_document_symbols(module, &doc.source);

    let recursive = syms
        .iter()
        .find(|s| s.name == "F" && s.detail.as_deref() == Some("RECURSIVE (arity 1)"))
        .expect("RECURSIVE declarations should appear in document symbols");
    assert_eq!(recursive.kind, SymbolKind::FUNCTION);

    let theorem = syms
        .iter()
        .find(|s| s.name == "T1")
        .expect("named THEOREM should appear in document symbols");
    assert_eq!(theorem.kind, SymbolKind::CLASS);
    assert_eq!(theorem.detail.as_deref(), Some("THEOREM"));

    let instance = syms
        .iter()
        .find(|s| s.name == "INSTANCE Sequences")
        .expect("INSTANCE unit should appear in document symbols");
    assert_eq!(instance.kind, SymbolKind::MODULE);

    let assume = syms
        .iter()
        .find(|s| s.name == "ASSUME")
        .expect("ASSUME unit should appear in document symbols");
    assert_eq!(assume.kind, SymbolKind::BOOLEAN);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_span_to_range() {
    use tla_core::FileId;
    let source = "line1\nline2\nline3";
    let span = tla_core::Span::new(FileId(0), 6, 11); // "line2"
    let range = position::span_to_range(source, span);

    assert_eq!(range.start.line, 1);
    assert_eq!(range.start.character, 0);
    assert_eq!(range.end.line, 1);
    assert_eq!(range.end.character, 5);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_error_diagnostics() {
    let mut doc = DocumentState::new("---- MODULE Broken ----\nVARIABLE".to_string());
    doc.analyze();

    // Should have parse errors — VARIABLE without identifier is invalid
    assert_eq!(
        doc.parse_errors.len(),
        1,
        "expected exactly 1 parse error for bare VARIABLE, got: {:?}",
        doc.parse_errors,
    );
    assert!(
        !doc.parse_errors[0].message.is_empty(),
        "parse error message should not be empty",
    );
    assert!(doc.module.is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_goto_definition() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let resolve = doc
        .resolve
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");

    // Find where 'x' variable is defined
    let x_var = resolve
        .symbols
        .iter()
        .find(|s| s.name == "x")
        .expect("x should be defined");
    let x_def_span = x_var.def_span;

    // Find 'Init' operator
    let init_sym = resolve
        .symbols
        .iter()
        .find(|s| s.name == "Init")
        .expect("Init should be defined");
    let init_def_span = init_sym.def_span;

    // Check references exist
    assert!(
        !resolve.references.is_empty(),
        "Should have some references"
    );

    // Find a reference to x - should resolve back to x's definition
    let x_ref = resolve
        .references
        .iter()
        .find(|(_, d)| *d == x_def_span)
        .expect("Should have at least one reference to x");
    let found_def = symbols::find_symbol_at_position(resolve, x_ref.0.start + 1);
    assert_eq!(found_def, Some(x_def_span));

    // Find a reference to Init - should resolve to Init's definition
    let init_ref = resolve
        .references
        .iter()
        .find(|(_, d)| *d == init_def_span)
        .expect("Should have at least one reference to Init");
    let found_def = symbols::find_symbol_at_position(resolve, init_ref.0.start + 1);
    assert_eq!(found_def, Some(init_def_span));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_references() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let resolve = doc
        .resolve
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");

    // Find 'x' variable definition
    let x_var = resolve
        .symbols
        .iter()
        .find(|s| s.name == "x")
        .expect("x should be defined");
    let x_def_span = x_var.def_span;

    // Find all references to x
    let refs = symbols::find_references_to_def(resolve, x_def_span);

    // x is used 4 times: Init(x = 0), Inc(x' = ... and ... = x + n), Spec(<<x, y>>)
    assert_eq!(
        refs.len(),
        4,
        "Expected exactly 4 references to x, found {}",
        refs.len()
    );
    for span in &refs {
        let found_def = symbols::find_symbol_at_position(resolve, span.start + 1);
        assert_eq!(
            found_def,
            Some(x_def_span),
            "reference span {:?} should resolve to x definition",
            span
        );
    }

    // Test that clicking on definition also finds references
    let def_span = symbols::find_definition_span_at_position(resolve, x_def_span.start + 1);
    assert_eq!(def_span, Some(x_def_span), "Should find definition span");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_references_from_reference() {
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let resolve = doc
        .resolve
        .as_ref()
        .expect("invariant: TEST_MODULE parses and resolves");

    // Find 'Inc' operator
    let inc_sym = resolve
        .symbols
        .iter()
        .find(|s| s.name == "Inc")
        .expect("Inc should be defined");
    let inc_def_span = inc_sym.def_span;

    // Inc is called twice in Next: "Inc(1) \/ Inc(2)"
    let refs = symbols::find_references_to_def(resolve, inc_def_span);
    assert_eq!(
        refs.len(),
        2,
        "Expected exactly 2 references to Inc, found {}",
        refs.len()
    );
    for span in &refs {
        let found_def = symbols::find_symbol_at_position(resolve, span.start + 1);
        assert_eq!(
            found_def,
            Some(inc_def_span),
            "reference span {:?} should resolve to Inc definition",
            span
        );
    }

    // Test finding definition from a reference position
    let (use_span, _) = resolve
        .references
        .iter()
        .find(|(_, d)| *d == inc_def_span)
        .expect("Should have at least one reference to Inc in references list");
    let found_def = symbols::find_definition_span_at_position(resolve, use_span.start + 1);
    assert_eq!(found_def, Some(inc_def_span));
}

// ───────────────────────────────────────────────────────────
// Diagnostic tests
// ───────────────────────────────────────────────────────────

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_unused_variable() {
    // y is declared but never referenced
    let source = r#"
---- MODULE UnusedVar ----
VARIABLE x, y
Init == x = 0
====
"#;
    let mut doc = DocumentState::new(source.to_string());
    doc.analyze();

    assert!(
        doc.parse_errors.is_empty(),
        "fixture should parse cleanly: {:?}",
        doc.parse_errors
    );

    let unused: Vec<_> = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
        .collect();

    assert_eq!(
        unused.len(),
        1,
        "expected 1 unused declaration (y), got {}: {:?}",
        unused.len(),
        unused.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    assert!(
        unused[0].message.contains("y"),
        "unused diagnostic should mention `y`, got: {}",
        unused[0].message
    );
    assert!(
        unused[0].message.contains("VARIABLE"),
        "unused diagnostic should mention VARIABLE, got: {}",
        unused[0].message
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_unused_constant() {
    let source = r#"
---- MODULE UnusedConst ----
CONSTANT A, B, C
VARIABLE x
Init == x = A
Next == x' = B
====
"#;
    let mut doc = DocumentState::new(source.to_string());
    doc.analyze();

    assert!(
        doc.parse_errors.is_empty(),
        "fixture should parse cleanly: {:?}",
        doc.parse_errors
    );

    let unused: Vec<_> = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
        .collect();

    assert_eq!(
        unused.len(),
        1,
        "expected 1 unused constant (C), got {}: {:?}",
        unused.len(),
        unused.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    assert!(
        unused[0].message.contains("C"),
        "unused diagnostic should mention `C`, got: {}",
        unused[0].message
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_unused_constant_n_in_test_module() {
    // TEST_MODULE declares CONSTANT N but never references it in any operator body.
    // This is a correct unused-declaration diagnostic.
    let mut doc = DocumentState::new(TEST_MODULE.to_string());
    doc.analyze();

    let unused: Vec<_> = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
        .collect();

    assert_eq!(
        unused.len(),
        1,
        "TEST_MODULE should flag N as unused, got: {:?}",
        unused.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    assert!(
        unused[0].message.contains("N"),
        "unused diagnostic should mention `N`, got: {}",
        unused[0].message
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_no_unused_when_all_referenced() {
    // Module where every VARIABLE and CONSTANT is referenced
    let source = r#"
---- MODULE AllUsed ----
EXTENDS Naturals
VARIABLE x, y
CONSTANT N
Init == x = 0 /\ y = N
====
"#;
    let mut doc = DocumentState::new(source.to_string());
    doc.analyze();

    let unused: Vec<_> = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
        .collect();

    assert!(
        unused.is_empty(),
        "all declarations are used, got unused: {:?}",
        unused.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_undefined_without_extends() {
    let source = r#"
---- MODULE NoExtends ----
VARIABLE x
Init == x = Bogus
====
"#;
    let mut doc = DocumentState::new(source.to_string());
    doc.analyze();

    assert!(
        doc.parse_errors.is_empty(),
        "fixture should parse cleanly: {:?}",
        doc.parse_errors
    );

    let undefined: Vec<_> = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UndefinedName)
        .collect();

    assert!(
        !undefined.is_empty(),
        "expected UndefinedName diagnostic for `Bogus` without EXTENDS"
    );
    assert!(
        undefined[0].message.contains("Bogus"),
        "diagnostic should mention `Bogus`, got: {}",
        undefined[0].message
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_possibly_undefined_with_extends() {
    let source = r#"
---- MODULE WithExtends ----
EXTENDS Naturals
VARIABLE x
Init == x = Bogus
====
"#;
    let mut doc = DocumentState::new(source.to_string());
    doc.analyze();

    assert!(
        doc.parse_errors.is_empty(),
        "fixture should parse cleanly: {:?}",
        doc.parse_errors
    );

    // With EXTENDS, undefined names should be "possibly undefined" (Warning), not Error
    let possibly: Vec<_> = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::PossiblyUndefined)
        .collect();

    assert!(
        !possibly.is_empty(),
        "expected PossiblyUndefined diagnostic for `Bogus` with EXTENDS"
    );

    // Should NOT have a hard UndefinedName error
    let hard: Vec<_> = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UndefinedName)
        .collect();
    assert!(
        hard.is_empty(),
        "should not have hard UndefinedName when EXTENDS present, got: {:?}",
        hard.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_version_tracking() {
    let source = r#"
---- MODULE Versioned ----
VARIABLE x
Init == x = 0
====
"#;
    let mut doc = DocumentState::with_version(source.to_string(), 5);
    doc.analyze();

    assert_eq!(doc.version, 5, "version should be preserved after analyze");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_parse_error_skips_analysis() {
    // A document with parse errors should not produce semantic diagnostics
    let mut doc = DocumentState::new("---- MODULE Broken ----\nVARIABLE".to_string());
    doc.analyze();

    assert!(!doc.parse_errors.is_empty(), "should have parse errors");
    assert!(
        doc.semantic_diagnostics.is_empty(),
        "parse errors should prevent semantic analysis, got: {:?}",
        doc.semantic_diagnostics
            .iter()
            .map(|d| &d.message)
            .collect::<Vec<_>>()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_semantic_diagnostics_reanalysis_clears_old() {
    // First analysis produces unused diagnostic
    let source1 = r#"
---- MODULE Reanalyze ----
VARIABLE x, y
Init == x = 0
====
"#;
    let mut doc = DocumentState::new(source1.to_string());
    doc.analyze();

    let unused_count = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
        .count();
    assert_eq!(
        unused_count, 1,
        "first analysis should produce 1 unused (y)"
    );

    // Re-analyze with fixed source that uses y
    doc.source = r#"
---- MODULE Reanalyze ----
VARIABLE x, y
Init == x = 0 /\ y = 0
====
"#
    .to_string();
    doc.analyze();

    let unused_count = doc
        .semantic_diagnostics
        .iter()
        .filter(|d| d.kind == SemanticDiagnosticKind::UnusedDeclaration)
        .count();
    assert_eq!(
        unused_count, 0,
        "re-analysis with y used should clear old unused diagnostic"
    );
}

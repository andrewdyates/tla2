// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Smoke tests for the BTOR2 parser.
//!
//! Validates basic parsing on hand-written programs and HWMCC'25 benchmarks.
//! Run with: cargo test -p tla-btor2 --test parse_smoke

use std::path::PathBuf;

use tla_btor2::parser::{parse, parse_file};
use tla_btor2::{Btor2Node, Btor2Sort};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Root directory for HWMCC'25 word-level BV benchmarks.
fn hwmcc_bv_dir() -> PathBuf {
    let home = std::env::var("HOME").expect("HOME environment variable not set");
    PathBuf::from(home).join("hwmcc/benchmarks/wordlevel/bv")
}

/// Returns the path to a specific HWMCC benchmark by its relative path
/// (as used in the results CSV, e.g. "2019/beem/bakery.3.prop1-func-interl.btor2").
fn hwmcc_benchmark(relative: &str) -> PathBuf {
    hwmcc_bv_dir().join(relative)
}

/// Skip a test if the HWMCC benchmarks directory is not available.
fn require_hwmcc() -> PathBuf {
    let dir = hwmcc_bv_dir();
    if !dir.exists() {
        panic!(
            "HWMCC benchmarks not found at {}. Set up ~/hwmcc/ to run these tests.",
            dir.display()
        );
    }
    dir
}

// ---------------------------------------------------------------------------
// Minimal hand-written programs
// ---------------------------------------------------------------------------

#[test]
fn test_parse_minimal_sorts_state_init_next_bad() {
    let src = "\
1 sort bitvec 1
2 sort bitvec 8
3 state 2 counter
4 zero 2
5 init 2 3 4
6 one 2
7 add 2 3 6
8 next 2 3 7
9 constd 2 10
10 ugt 1 3 9
11 bad 10
";
    let prog = parse(src).expect("minimal program should parse");

    // Sorts.
    assert_eq!(prog.sorts.len(), 2);
    assert!(matches!(prog.sorts[&1], Btor2Sort::BitVec(1)));
    assert!(matches!(prog.sorts[&2], Btor2Sort::BitVec(8)));

    // State/input counts.
    assert_eq!(prog.num_states, 1);
    assert_eq!(prog.num_inputs, 0);

    // Bad property.
    assert_eq!(prog.bad_properties.len(), 1);
    assert_eq!(prog.bad_properties[0], 11);

    // Total lines.
    assert_eq!(prog.lines.len(), 11);
}

#[test]
fn test_parse_with_comments_and_blanks() {
    let src = "\
; BTOR2 test file
; Author: test

1 sort bitvec 1

; state declaration follows
2 state 1 toggle
3 zero 1
4 init 1 2 3
5 not 1 2
6 next 1 2 5

; property
7 bad 2
";
    let prog = parse(src).expect("comments and blanks should be skipped");
    assert_eq!(prog.lines.len(), 7);
    assert_eq!(prog.num_states, 1);
    assert_eq!(prog.bad_properties, vec![7]);
}

#[test]
fn test_parse_inline_comments() {
    // Some HWMCC benchmarks (e.g., hkust 2025) have inline comments after data.
    let src = "\
1 sort bitvec 1
2 input 1 clk ; /path/to/source.v:42
3 input 1 rst ; /path/to/source.v:43
4 and 1 2 3
5 bad 4
";
    let prog = parse(src).expect("inline comments should be handled");
    assert_eq!(prog.num_inputs, 2);
    assert_eq!(prog.lines.len(), 5);

    // Verify symbols parsed correctly (should NOT include the comment text).
    let input_line = &prog.lines[1];
    match &input_line.node {
        Btor2Node::Input(_, sym) => {
            assert_eq!(
                sym.as_deref(),
                Some("clk"),
                "symbol should be 'clk' not include comment"
            );
        }
        other => panic!("expected Input node, got: {other:?}"),
    }
}

#[test]
fn test_parse_array_sort_program() {
    let src = "\
1 sort bitvec 8
2 sort bitvec 32
3 sort array 1 2
4 input 3 memory
5 constd 1 0
6 read 2 4 5
7 constd 2 42
8 eq 1 6 7
9 write 3 4 5 7
10 bad 8
";
    let prog = parse(src).expect("array program should parse");
    assert_eq!(prog.sorts.len(), 3);
    assert!(matches!(
        &prog.sorts[&3],
        Btor2Sort::Array { index, element }
        if matches!(index.as_ref(), Btor2Sort::BitVec(8))
            && matches!(element.as_ref(), Btor2Sort::BitVec(32))
    ));
    assert_eq!(prog.num_inputs, 1);
}

#[test]
fn test_parse_negated_operands() {
    let src = "\
1 sort bitvec 1
2 input 1 a
3 input 1 b
4 and 1 -2 -3
5 bad 4
";
    let prog = parse(src).expect("negated operands should parse");
    let and_line = &prog.lines[3];
    assert_eq!(and_line.args, vec![-2, -3]);
}

#[test]
fn test_parse_constraint_and_fair() {
    let src = "\
1 sort bitvec 1
2 input 1 clk
3 constraint 2
4 fair 2
5 bad 2
";
    let prog = parse(src).expect("constraint and fair should parse");
    assert_eq!(prog.constraints, vec![3]);
    assert_eq!(prog.fairness, vec![4]);
    assert_eq!(prog.bad_properties, vec![5]);
}

#[test]
fn test_parse_empty_program() {
    let prog = parse("").expect("empty input should parse");
    assert!(prog.lines.is_empty());
    assert_eq!(prog.num_states, 0);
    assert_eq!(prog.num_inputs, 0);
}

#[test]
fn test_parse_error_unknown_opcode() {
    let result = parse("1 sort bitvec 1\n2 frobnicate 1 1\n");
    assert!(result.is_err(), "unknown opcode should produce error");
}

#[test]
fn test_parse_error_duplicate_id() {
    let result = parse("1 sort bitvec 1\n1 sort bitvec 8\n");
    assert!(result.is_err(), "duplicate id should produce error");
}

// ---------------------------------------------------------------------------
// HWMCC'25 BEEM benchmark tests
// ---------------------------------------------------------------------------

#[test]
fn test_parse_hwmcc_bakery3() {
    let _ = require_hwmcc();
    let path = hwmcc_benchmark("2019/beem/bakery.3.prop1-func-interl.btor2");
    let prog = parse_file(&path).unwrap_or_else(|e| panic!("failed to parse bakery.3: {e}"));

    // Expected counts from manual inspection of the benchmark file.
    assert_eq!(
        prog.num_states, 28,
        "bakery.3 should have 28 state variables"
    );
    assert_eq!(prog.num_inputs, 24, "bakery.3 should have 24 inputs");
    assert_eq!(
        prog.bad_properties.len(),
        1,
        "bakery.3 should have 1 bad property"
    );
    assert_eq!(
        prog.constraints.len(),
        0,
        "bakery.3 should have 0 constraints"
    );

    // 4 sort definitions: bitvec 1, 8, 24, 32.
    assert_eq!(prog.sorts.len(), 4, "bakery.3 should have 4 sorts");
    assert!(matches!(prog.sorts[&1], Btor2Sort::BitVec(1)));
    assert!(matches!(prog.sorts[&2], Btor2Sort::BitVec(8)));

    // Total parseable lines (excluding comments/blanks): 504.
    assert_eq!(prog.lines.len(), 504, "bakery.3 should have 504 IR lines");
}

#[test]
fn test_parse_hwmcc_collision1() {
    let _ = require_hwmcc();
    let path = hwmcc_benchmark("2019/beem/collision.1.prop1-func-interl.btor2");
    let prog = parse_file(&path).unwrap_or_else(|e| panic!("failed to parse collision.1: {e}"));

    assert_eq!(
        prog.num_states, 27,
        "collision.1 should have 27 state variables"
    );
    assert_eq!(prog.num_inputs, 31, "collision.1 should have 31 inputs");
    assert_eq!(
        prog.bad_properties.len(),
        1,
        "collision.1 should have 1 bad property"
    );
}

#[test]
fn test_parse_hwmcc_brp2() {
    let _ = require_hwmcc();
    let path = hwmcc_benchmark("2019/beem/brp2.3.prop3-func-interl.btor2");
    let prog = parse_file(&path).unwrap_or_else(|e| panic!("failed to parse brp2.3: {e}"));

    assert_eq!(prog.num_states, 44, "brp2.3 should have 44 state variables");
    assert_eq!(prog.num_inputs, 33, "brp2.3 should have 33 inputs");
    assert_eq!(
        prog.bad_properties.len(),
        1,
        "brp2.3 should have 1 bad property"
    );
}

#[test]
fn test_parse_hwmcc_exit3() {
    let _ = require_hwmcc();
    let path = hwmcc_benchmark("2019/beem/exit.3.prop1-back-serstep.btor2");
    let prog = parse_file(&path).unwrap_or_else(|e| panic!("failed to parse exit.3: {e}"));

    assert_eq!(prog.num_states, 52, "exit.3 should have 52 state variables");
    assert_eq!(prog.num_inputs, 139, "exit.3 should have 139 inputs");
    assert_eq!(
        prog.bad_properties.len(),
        1,
        "exit.3 should have 1 bad property"
    );
}

#[test]
fn test_parse_hwmcc_pgm_protocol8() {
    let _ = require_hwmcc();
    let path = hwmcc_benchmark("2019/beem/pgm_protocol.8.prop6-func-interl.btor2");
    let prog = parse_file(&path).unwrap_or_else(|e| panic!("failed to parse pgm_protocol.8: {e}"));

    assert_eq!(
        prog.num_states, 178,
        "pgm_protocol.8 should have 178 state variables"
    );
    assert_eq!(
        prog.num_inputs, 120,
        "pgm_protocol.8 should have 120 inputs"
    );
    assert_eq!(
        prog.bad_properties.len(),
        1,
        "pgm_protocol.8 should have 1 bad property"
    );
}

#[test]
fn test_parse_hwmcc_simple_alu() {
    let _ = require_hwmcc();
    let path = hwmcc_benchmark("2020/mann/simple_alu.btor2");
    let prog = parse_file(&path).unwrap_or_else(|e| panic!("failed to parse simple_alu: {e}"));

    assert_eq!(
        prog.num_states, 3,
        "simple_alu should have 3 state variables"
    );
    assert_eq!(prog.num_inputs, 4, "simple_alu should have 4 inputs");
    assert_eq!(
        prog.bad_properties.len(),
        1,
        "simple_alu should have 1 bad property"
    );
    assert_eq!(prog.sorts.len(), 3, "simple_alu should have 3 sorts");
    assert_eq!(prog.lines.len(), 36, "simple_alu should have 36 IR lines");
}

/// Verify that ALL BEEM benchmarks parse without errors.
#[test]
fn test_parse_all_beem_benchmarks() {
    let _ = require_hwmcc();
    let beem_dir = hwmcc_bv_dir().join("2019/beem");

    let entries: Vec<_> = std::fs::read_dir(&beem_dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", beem_dir.display()))
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "btor2"))
        .collect();

    assert!(
        !entries.is_empty(),
        "expected BEEM benchmarks in {}",
        beem_dir.display()
    );

    let mut failures = Vec::new();
    for entry in &entries {
        let path = entry.path();
        if let Err(e) = parse_file(&path) {
            failures.push(format!("{}: {e}", path.display()));
        }
    }

    assert!(
        failures.is_empty(),
        "failed to parse {} BEEM benchmark(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

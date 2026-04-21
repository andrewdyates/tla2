// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for global and set constraints: set_in_reif, array_int_maximum,
// array_int_minimum, int_lin_ne_reif, variable RHS, bool_and_reif,
// bool_or_reif.

use std::collections::HashMap;

use super::tests::solve_cp_output;

// --- set_in_reif tests ---

#[test]
fn test_set_in_reif_sparse_true() {
    // r ↔ (x ∈ {1, 3}), x = 3 → r = true.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, {1, 3}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_sparse_false() {
    // r ↔ (x ∈ {1, 3}), x = 2 → r = false.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, {1, 3}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_interval_true() {
    // r ↔ (x ∈ 1..3), x = 2 → r = true.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, 1..3, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_interval_false() {
    // r ↔ (x ∈ 1..3), x = 5 → r = false.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 5);\n\
        constraint set_in_reif(x, 1..3, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

// --- set_in_reif with empty set ---

#[test]
fn test_set_in_reif_empty_set() {
    // r ↔ (x ∈ {}), x = 3 → r = false (empty set has no members).
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, {}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_empty_set() {
    // Named empty set parameter: S = {}, x = 3 → r = false.
    let fzn = "\
        set of int: S = {};\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

// --- set_in_reif with named set parameter (Ident resolution) ---

#[test]
fn test_set_in_reif_ident_sparse_true() {
    // Named set parameter: S = {1, 3}, x = 3 → r = true.
    let fzn = "\
        set of int: S = {1, 3};\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_sparse_false() {
    // Named set parameter: S = {1, 3}, x = 2 → r = false.
    let fzn = "\
        set of int: S = {1, 3};\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_range_true() {
    // Named set parameter: S = 1..3, x = 2 → r = true.
    let fzn = "\
        set of int: S = 1..3;\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_range_false() {
    // Named set parameter: S = 1..3, x = 5 → r = false.
    let fzn = "\
        set of int: S = 1..3;\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 5);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

// --- set_in_reif with large domain (indicator variable path) ---

#[test]
fn test_set_in_reif_large_domain_true() {
    // Domain > 10000 forces indicator variable path.
    // r ↔ (x ∈ {100, 500}), x = 500 → r = true.
    let fzn = "\
        var 1..20000: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 500);\n\
        constraint set_in_reif(x, {100, 500}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_large_domain_false() {
    // Domain > 10000 forces indicator variable path.
    // r ↔ (x ∈ {100, 500}), x = 300 → r = false.
    let fzn = "\
        var 1..20000: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 300);\n\
        constraint set_in_reif(x, {100, 500}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_large_domain_single_element() {
    // Single element in large domain: r ↔ (x ∈ {42}), x = 42 → r = true.
    let fzn = "\
        var 1..11000: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 42);\n\
        constraint set_in_reif(x, {42}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

// --- int_lin_ne_reif tests ---

#[test]
fn test_int_lin_ne_reif_true() {
    // r ↔ (x + y ≠ 0), x = 0, y = 1 → r = true.
    let fzn = "\
        var 0..0: x :: output_var;\n\
        var -1..1: y :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(y, 1);\n\
        constraint int_lin_ne_reif([1, 1], [x, y], 0, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_int_lin_ne_reif_false() {
    // r ↔ (x + y ≠ 0), x = 0, y = 0 → r = false.
    let fzn = "\
        var 0..0: x :: output_var;\n\
        var 0..0: y :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_lin_ne_reif([1, 1], [x, y], 0, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

// --- array_int_maximum tests ---

#[test]
fn test_array_int_maximum() {
    // r = max([a, b]), a = 3, b = 7 → r = 7.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 3);\n\
        constraint int_eq(b, 7);\n\
        constraint array_int_maximum(r, [a, b]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 7;"), "output: {output}");
}

#[test]
fn test_array_int_maximum_three() {
    // r = max([2, 8, 5]) → r = 8.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 2);\n\
        constraint int_eq(b, 8);\n\
        constraint int_eq(c, 5);\n\
        constraint array_int_maximum(r, [a, b, c]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 8;"), "output: {output}");
}

// --- array_int_minimum tests ---

#[test]
fn test_array_int_minimum() {
    // r = min([a, b]), a = 3, b = 7 → r = 3.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 3);\n\
        constraint int_eq(b, 7);\n\
        constraint array_int_minimum(r, [a, b]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 3;"), "output: {output}");
}

#[test]
fn test_array_int_minimum_three() {
    // r = min([9, 4, 6]) → r = 4.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 9);\n\
        constraint int_eq(b, 4);\n\
        constraint int_eq(c, 6);\n\
        constraint array_int_minimum(r, [a, b, c]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 4;"), "output: {output}");
}

// --- Variable RHS linear test ---

#[test]
fn test_linear_eq_variable_rhs() {
    // bool_lin_eq([-1, 2, 3], [x1, x2, x3], eq) where eq is a variable.
    let fzn = "\
        array [1..3] of int: cs = [-1, 2, 3];\n\
        var bool: x1 :: output_var;\n\
        var bool: x2 :: output_var;\n\
        var bool: x3 :: output_var;\n\
        var 1..3: eq :: output_var;\n\
        constraint bool_lin_eq(cs, [x1, x2, x3], eq);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    // Verify the equation holds: -1*x1 + 2*x2 + 3*x3 = eq
    let mut vals: HashMap<&str, i64> = HashMap::new();
    for line in output.lines() {
        for name in &["x1", "x2", "x3", "eq"] {
            if let Some(rest) = line.strip_prefix(&format!("{name} = ")) {
                if let Some(val_str) = rest.strip_suffix(';') {
                    let v = match val_str {
                        "true" => 1,
                        "false" => 0,
                        s => s.parse().unwrap(),
                    };
                    vals.insert(name, v);
                }
            }
        }
    }
    assert_eq!(vals.len(), 4, "should find all 4 values, output:\n{output}");
    let lhs = -vals["x1"] + 2 * vals["x2"] + 3 * vals["x3"];
    assert_eq!(
        lhs, vals["eq"],
        "equation should hold: {lhs} != {}",
        vals["eq"]
    );
}

// --- bool_and_reif tests ---

#[test]
fn test_bool_and_reif() {
    // r ↔ (a ∧ b), a = true, b = false → r = false.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, false);\n\
        constraint bool_and_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_bool_and_reif_true() {
    // r ↔ (a ∧ b), a = true, b = true → r = true.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, true);\n\
        constraint bool_and_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

// --- bool_or_reif tests ---

#[test]
fn test_bool_or_reif() {
    // r ↔ (a ∨ b), a = false, b = false → r = false.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, false);\n\
        constraint bool_eq(b, false);\n\
        constraint bool_or_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_bool_or_reif_true() {
    // r ↔ (a ∨ b), a = false, b = true → r = true.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, false);\n\
        constraint bool_eq(b, true);\n\
        constraint bool_or_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

// --- circuit tests ---

#[test]
fn test_circuit_4() {
    // circuit([x1, x2, x3, x4]): Hamiltonian cycle on 4 nodes.
    let fzn = "\
        var 1..4: x1 :: output_var;\n\
        var 1..4: x2 :: output_var;\n\
        var 1..4: x3 :: output_var;\n\
        var 1..4: x4 :: output_var;\n\
        constraint fzn_circuit([x1, x2, x3, x4]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    // Parse the solution and verify it forms a single cycle
    let vals = parse_int_values(&output, &["x1", "x2", "x3", "x4"]);
    assert_eq!(vals.len(), 4, "should find all 4 values, output:\n{output}");
    // No self-loops
    for i in 0..4 {
        let name = &["x1", "x2", "x3", "x4"][i];
        assert_ne!(vals[name], (i + 1) as i64, "no self-loop at {name}");
    }
    // All different
    let mut seen: Vec<i64> = vals.values().copied().collect();
    seen.sort_unstable();
    assert_eq!(seen, [1, 2, 3, 4], "must be a permutation");
    // Verify single cycle: starting from node 1, follow successors, must visit all nodes
    let mut visited = [false; 4];
    let mut current = 0; // node 1 (0-indexed)
    for _ in 0..4 {
        assert!(!visited[current], "revisiting node {}", current + 1);
        visited[current] = true;
        let succ = vals[&["x1", "x2", "x3", "x4"][current]] as usize - 1;
        current = succ;
    }
    assert_eq!(current, 0, "cycle must return to node 1");
    assert!(visited.iter().all(|&v| v), "all nodes must be visited");
}

#[test]
fn test_circuit_no_subcycles() {
    // circuit([x1, x2, x3, x4]) with x1=2, x2=1 forced.
    // Without circuit, this allows subcycles {1,2} + {3,4}.
    // With circuit, nodes 3 and 4 must connect to/from the {1,2} chain.
    let fzn = "\
        var 1..4: x1 :: output_var;\n\
        var 1..4: x2 :: output_var;\n\
        var 1..4: x3 :: output_var;\n\
        var 1..4: x4 :: output_var;\n\
        constraint fzn_circuit([x1, x2, x3, x4]);\n\
        constraint int_eq(x1, 2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    let vals = parse_int_values(&output, &["x1", "x2", "x3", "x4"]);
    assert_eq!(vals["x1"], 2);
    // x2 cannot be 1 (would create subcycle {1,2}), must link to 3 or 4
    assert_ne!(vals["x2"], 1, "x2=1 would create subcycle {{1,2}}");
}

// --- inverse tests ---

#[test]
fn test_inverse_3() {
    // inverse(x, y): x[y[i]] = i and y[x[i]] = i for all i.
    let fzn = "\
        var 1..3: x1 :: output_var;\n\
        var 1..3: x2 :: output_var;\n\
        var 1..3: x3 :: output_var;\n\
        var 1..3: y1 :: output_var;\n\
        var 1..3: y2 :: output_var;\n\
        var 1..3: y3 :: output_var;\n\
        constraint fzn_inverse([x1, x2, x3], [y1, y2, y3]);\n\
        constraint int_eq(x1, 3);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    let vals = parse_int_values(&output, &["x1", "x2", "x3", "y1", "y2", "y3"]);
    assert_eq!(vals.len(), 6, "should find all 6 values, output:\n{output}");
    assert_eq!(vals["x1"], 3);
    // Verify inverse property: x[y[i]] = i
    let x = [vals["x1"], vals["x2"], vals["x3"]];
    let y = [vals["y1"], vals["y2"], vals["y3"]];
    for i in 0..3usize {
        let expected = (i + 1) as i64;
        let yi = y[i] as usize - 1;
        assert_eq!(
            x[yi],
            expected,
            "x[y[{}]] = {} (expected {})",
            i + 1,
            x[yi],
            expected
        );
        let xi = x[i] as usize - 1;
        assert_eq!(
            y[xi],
            expected,
            "y[x[{}]] = {} (expected {})",
            i + 1,
            y[xi],
            expected
        );
    }
}

/// Parse integer values from DZN output.
fn parse_int_values<'a>(output: &str, names: &'a [&'a str]) -> HashMap<&'a str, i64> {
    let mut vals = HashMap::new();
    for line in output.lines() {
        for &name in names {
            if let Some(rest) = line.strip_prefix(&format!("{name} = ")) {
                if let Some(val_str) = rest.strip_suffix(';') {
                    let v: i64 = val_str.parse().unwrap_or_else(|_| match val_str {
                        "true" => 1,
                        "false" => 0,
                        _ => panic!("cannot parse {val_str}"),
                    });
                    vals.insert(name, v);
                }
            }
        }
    }
    vals
}
